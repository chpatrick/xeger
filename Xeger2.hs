{-# LANGUAGE GeneralizedNewtypeDeriving, NamedFieldPuns, TemplateHaskell, ScopedTypeVariables, TupleSections #-}

import Control.Applicative hiding (some, many)
import Control.Lens
import Control.Monad.Cont
import Control.Monad.RWS
import Data.Foldable
import Data.SBV
import Data.SBV.Internals (genMkSymVar, genLiteral, genFromCW)
import Data.Traversable

int :: (Integral i, Num a) => i -> a
int = fromIntegral

charKind :: Kind
charKind = KBounded False 8

instance HasKind Char where
  kindOf _ = charKind

instance SymWord Char where
  mkSymWord = genMkSymVar charKind
  literal c
    | 0 <= ic && ic < 256 = genLiteral charKind ic
    | otherwise = error "ASCII only"
      where ic = fromEnum c
  fromCW = toEnum . genFromCW
  mbMaxBound = Just (toEnum 255)
  mbMinBound = Just (toEnum 0)

instance SatModel Char where
  parseCWs cws = (\(cb, cws') -> ( toEnum $ int (cb :: Word8), cws' )) <$> parseCWs cws

type SymIndex = Word8
type SIndex = SBV SymIndex
type SChar = SBV Char

type GetChar = SIndex -> SChar

data MatchContext = MatchContext
  { _matchLength :: Int
  , _charF :: GetChar
  }

makeLenses ''MatchContext

newtype MatchState = MatchState { _matchPos :: SIndex }
  deriving ( Show, Mergeable )

makeLenses ''MatchState

newtype SAnd = SAnd SBool
  deriving (Boolean, Mergeable)

instance Monoid SAnd where
  mempty = true
  mappend = (&&&)

newtype Match r a = Match (ContT r (RWST MatchContext SAnd MatchState Maybe) a)
  deriving (Functor, Applicative, Monad, MonadReader MatchContext, MonadState MatchState)

instance Mergeable r => Alternative (Match r) where
  empty = Match $ ContT $ \_ -> empty
  Match l <|> Match r
    = Match $ ContT $ \cc -> RWST $ \ctx s ->
      let run m = runRWST (runContT m cc) ctx s in
      case ( run l, run r ) of
        ( lr @ (Just ( _, _, SAnd p )), rr @ (Just _) ) -> ite p lr rr
        ( lr @ (Just _), _ ) -> lr
        ( _, rr @ (Just _) ) -> rr
        _ -> Nothing

instance Mergeable r => MonadPlus (Match r) where
  mzero = empty
  mplus = (<|>)

runMatch :: GetChar -> Int -> Match a a -> SBool
runMatch gc n (Match m) =
  let ctx = MatchContext { _matchLength = n, _charF = gc }
      s = MatchState 0
  in case execRWST (runContT m return) ctx s of
      Just ( _, SAnd p ) -> p
      Nothing -> false

sguard :: SBool -> Match r ()
sguard = Match . lift . tell . SAnd

anyChar :: Match r SChar
anyChar = do
  p <- use matchPos
  len <- view matchLength
  gc <- view charF
  sguard $ p .< int len
  matchPos .= p + 1
  return (gc p)

char :: Char -> Match r ()
char pc = anyChar >>= \c -> sguard $ c .== literal pc

many :: Mergeable r => Match r () -> Match r ()
many m = do
  depth <- view matchLength
  let star' 0 = return ()
      star' n = (m >> star' (n - 1)) <|> return ()
  star' depth

eof :: Match r ()
eof = do
  p <- use matchPos
  len <- view matchLength
  sguard $ p .== int len

data Group = Group { groupStart :: SIndex, groupLength :: SIndex }

group :: Match r () -> Match r Group
group m = do
  start <- use matchPos
  m
  end <- use matchPos
  return $ Group start (end - start)

backref :: Group -> Match r ()
backref Group { groupStart = gstart, groupLength = glen } = do
  pos <- use matchPos
  len <- view matchLength
  gc <- view charF
  let is = map int [0..len - 1]
  sguard $ pos + glen .<= int len &&& bAll (\i -> i .< glen ==> gc (pos + i) .== gc (gstart + i)) is
  matchPos += glen

-- puzzle types

type Puzzle c = ( Predicate, [ ( c, String ) ] )

linear :: Int -> Match () () -> Puzzle Int
linear n m
  = ( p, charVars )
    where
      charVars = [ ( i, "char_" ++ show i ) | i <- [0..n - 1] ]
      p = do
        chars :: SArray SymIndex Char <- newArray_ Nothing
        let getc = readArray chars
            pp = runMatch getc n (m >> eof)
        vps <- for charVars $ \( i, vn ) -> do
          v <- free vn
          return $ v .== getc (int i)
        return $ pp &&& bAnd vps

-- Solving
getResultChars :: SatResult -> [ ( c, String ) ] -> Maybe [ ( c, Char ) ]
getResultChars res@(SatResult (Satisfiable _ _)) vs
  = for vs $ \( i, vn ) -> ( i, ) <$> getModelValue vn res
getResultChars _ _ = Nothing

satChars :: Puzzle c -> IO (Maybe [ ( c, Char ) ])
satChars ( p, vs ) = do
  res <- sat p
  return $ getResultChars res vs

-- Utility
dumpSMT :: Puzzle c -> IO ()
dumpSMT ( p, _ )
  = compileToSMTLib True True p >>= putStr