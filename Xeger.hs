module Xeger where

import Control.Applicative hiding (some, many)
import Data.Char
import Control.Lens
import Control.Monad.Cont
import Control.Monad.RWS.Strict hiding (Alt)
import Control.Monad.State.Strict
import Data.Aeson hiding ((.=))
import Data.Aeson.Types hiding ((.=))
import Data.Foldable
import qualified Data.IntMap.Strict as IM
import Data.Maybe
import Data.SBV
import Data.SBV.Internals (genMkSymVar, genLiteral, genFromCW)
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Vector as V
import Data.String
import Data.Traversable
import Network.HTTP.Conduit
import Text.Regex.TDFA.Pattern
import Text.Regex.TDFA.ReadRegex

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

newtype Match a = Match (ContT () (RWS MatchContext SAnd MatchState) a)
  deriving (Functor, Applicative, Monad, MonadReader MatchContext, MonadState MatchState)

instance Alternative Match where
  empty = Match $ ContT $ const (tell false)
  Match l <|> Match r
    = Match $ ContT $ \cc -> rws $ \ctx s ->
      let run m = runRWS (runContT m cc) ctx s
      in case run l of
        ( _, _, SAnd p ) -> ite p (run l) (run r)

instance MonadPlus Match where
  mzero = empty
  mplus = (<|>)

runMatch :: GetChar -> Int -> Match a -> SBool
runMatch gc n m =
  let ctx = MatchContext { _matchLength = n, _charF = gc }
      s = MatchState 0
      Match cm = m >> eof
  in case execRWS (runContT cm return) ctx s of
      ( _, SAnd p ) -> p

sguard :: SBool -> Match ()
sguard = Match . lift . tell . SAnd

anyChar :: Match SChar
anyChar = do
  p <- use matchPos
  len <- view matchLength
  gc <- view charF
  sguard $ p .< int len
  matchPos .= p + 1
  return (gc p)

char :: Char -> Match ()
char pc = anyChar >>= \c -> sguard $ c .== literal pc

oneOf :: [ Char ] -> Match ()
oneOf pcs = anyChar >>= \c -> sguard $ c `sElem` map literal pcs

many :: Match () -> Match ()
many m = do
  depth <- view matchLength
  let star' 0 = return ()
      star' n = (m >> star' (n - 1)) <|> return ()
  star' depth

eof :: Match ()
eof = do
  p <- use matchPos
  len <- view matchLength
  sguard $ p .== int len

data Group = Group { groupStart :: SIndex, groupLength :: SIndex }

group :: Match a -> Match ( a, Group )
group m = do
  start <- use matchPos
  x <- m
  end <- use matchPos
  return ( x, Group start (end - start) )

group_ :: Match a -> Match Group
group_ m = snd <$> group m

backref :: Group -> Match ()
backref Group { groupStart = gstart, groupLength = glen } = do
  pos <- use matchPos
  len <- view matchLength
  gc <- view charF
  let is = map int [0..len - 1]
  sguard $ pos + glen .<= int len &&& bAll (\i -> i .< glen ==> gc (pos + i) .== gc (gstart + i)) is
  matchPos += glen

-- puzzle types

type Puzzle c = ( Predicate, [ ( c, String ) ] )

linear :: Int -> Match () -> Puzzle Int
linear n m
  = ( p, charVars )
    where
      charVars = [ ( i, "char_" ++ show i ) | i <- [0..n - 1] ]
      p = do
        chars :: SArray SymIndex Char <- newArray_ Nothing
        let getc = readArray chars
            pp = runMatch getc n m
        vps <- for charVars $ \( i, vn ) -> do
          v <- free vn
          return $ v .== getc (int i)
        return $ pp &&& bAnd vps

crossword :: [ Match () ] -> [ Match () ] -> Puzzle ( Int, Int )
crossword horizPs vertPs
  = ( p, charVars )
    where
      width = length horizPs
      height = length vertPs
      charVars = [ ( ( x, y ), "char_" ++ show x ++ "_" ++ show y ) | y <- [0..height - 1], x <- [0..width - 1] ]
      p = do
        chars :: SArray SymIndex Char <- newArray_ Nothing
        let getc = readArray chars
            coords = [0 :: Int ..]
            horizPreds = [ runMatch getColumn height (hp >> eof)
                         | ( x, hp ) <- zip coords horizPs
                         , let getColumn y = getc (int width * y + int x)
                         ]
            vertPreds = [ runMatch getRow width (vp >> eof)
                        | ( y, vp ) <- zip coords vertPs
                        , let getRow x = getc (int (width * y) + x)
                        ]
        vps <- for charVars $ \( ( x, y ), vn ) -> do
          v <- free vn
          return $ v .== getc (int (y * width + x))
        return $ bAnd horizPreds &&& bAnd vertPreds &&& bAnd vps

-- Solving
getResultChars :: Modelable m => [ ( c, String ) ] -> m -> Maybe [ ( c, Char ) ]
getResultChars vs m = do
  guard (modelExists m)
  for vs $ \( i, vn ) -> ( i, ) <$> getModelValue vn m

satChars :: Puzzle c -> IO (Maybe [ ( c, Char ) ])
satChars ( p, vs ) = do
  res <- sat p
  return $ getResultChars vs res

allSatChars :: Puzzle c -> IO [ [ ( c, Char ) ] ]
allSatChars ( p, vs ) = do
  AllSatResult ( _, ress ) <- allSat p
  return $ mapMaybe (getResultChars vs) ress

-- Utility
dumpSMT :: Puzzle c -> IO ()
dumpSMT ( p, _ )
  = compileToSMTLib True True p >>= putStr

linAllChars :: IO [ [ ( Int, Char ) ] ] -> IO [ String ]
linAllChars = fmap (map (map snd))

-- Regex
instance IsString Pattern where
  fromString s = case parseRegex s of
    Right ( p, _ ) -> p

patternSetChars :: PatternSet -> [ Char ]
patternSetChars (PatternSet (Just scs) Nothing Nothing Nothing)
  = S.toList scs
patternSetChars _ = error "Unsupported pattern set."

regex :: Pattern -> Match ()
regex pat = evalStateT (matchPat (starTrans pat)) IM.empty
  where
    matchPat = \case
      PEmpty -> return ()
      PGroup Nothing p -> matchPat p
      PGroup (Just gi) p -> do
        start <- lift $ use matchPos
        matchPat p
        end <- lift $ use matchPos
        at gi .= Just (Group start (end - start))
      POr ps -> asum $ map matchPat ps
      PConcat ps -> traverse_ matchPat ps
      PStar _ p -> do
        depth <- lift $ view matchLength
        let m = matchPat p
            star' 0 = return ()
            star' n = (m >> star' (n - 1)) <|> return ()
        star' depth
      PDot _ -> lift $ void anyChar
      PAny _ ps -> lift $ oneOf $ patternSetChars ps
      PAnyNot _ ps -> lift $ do
        c <- anyChar
        sguard $ bnot $ c `sElem` map literal (patternSetChars ps)
      PChar _ pc -> lift $ do
        c <- anyChar
        sguard $ c .== literal pc
      PEscape _ esc -> case esc of
        _ | isDigit esc -> do
          m'g <- use $ at $ digitToInt esc
          case m'g of
            Just g -> lift $ backref g
            Nothing -> empty
        'd' -> lift $ oneOf ['0'..'9']
      PNonCapture p -> matchPat p
      x -> error $ "Unsupported pattern: " ++ show x

-- Do a crossword

doCrossword :: [ Pattern ] -> [ Pattern ] -> IO ()
doCrossword horizPs vertPs =
  satChars (crossword (map regex horizPs) (map regex vertPs)) >>= \case
    Nothing -> putStrLn "No solution found :("
    Just ls -> putStr $ unlines
      [ [ l | x <- [0..length horizPs - 1], let Just l = lookup ( x, y ) ls  ]
      | y <- [0..length vertPs - 1]
      ]

-- regexcrosswords.com loading

type Challenge = ( [ String ], [ String ] )

parseChallenge :: Object -> Parser ( String, Challenge )
parseChallenge puzz = do
  pn <- puzz .: "name"
  patternsX <- puzz .: "patternsX"
  patternsY <- puzz .: "patternsY"
  return ( T.unpack pn, ( map (T.unpack . V.head) patternsX, map (T.unpack . V.head) patternsY ) )

parseChallenges :: [ Object ] -> Parser [ ( String, Challenge ) ]
parseChallenges cSets = do
  pSets <- for (cSets :: [Object]) $ \cSet -> do
    ps <- cSet .: "puzzles"
    for (ps :: [Object]) parseChallenge
  return $ concat pSets

doChallenge :: String -> IO ()
doChallenge puzzleName = do
  cjson <- simpleHttp "http://regexcrossword.com/data/challenges.json"
  let Just cSets = decode cjson
      Just challenges = parseMaybe parseChallenges cSets
      Just ( h, v ) = lookup puzzleName challenges
  doCrossword (map fromString h) (map fromString v)

doPlayerChallenge :: String -> IO ()
doPlayerChallenge puzzleId = do
  cjson <- simpleHttp $ "http://regexcrossword.com/api/puzzles?puzzle_id=" ++ puzzleId
  let Just c = decode cjson
      Just ( _, ( h, v ) ) = parseMaybe parseChallenge c
  doCrossword (map fromString h) (map fromString v)