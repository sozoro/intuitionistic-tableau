{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import           Control.Arrow                ((&&&))
import           Control.Monad                (guard)
import           Data.Char                    (isSpace)
import           Data.List                    (groupBy, intercalate)
import qualified Data.Map                     as M
import           Data.Maybe                   (listToMaybe)
import qualified Data.Set                     as S
import           Numeric.Natural
import           System.Environment           (getArgs)
import qualified Text.ParserCombinators.ReadP as P

-- https://www.lfcs.inf.ed.ac.uk/reports/95/ECS-LFCS-95-321/

data Atom a = Top
            | Bot
            | Pure a
            deriving (Eq, Ord, Functor)

instance Show a => Show (Atom a) where
  show Top      = "⊤"
  show Bot      = "⊥"
  show (Pure a) = show a

data Formula a = Atom (Atom a)
               | And  (Formula a) (Formula a)
               | Or   (Formula a) (Formula a)
               | Impl (Formula a) (Formula a)
               deriving (Eq, Ord, Functor)

formulaParen :: Show a => Formula a -> String
formulaParen x@(Atom _) = show x
formulaParen x          = "(" ++ show x ++ ")"

instance Show a => Show (Formula a) where
  show (Atom a)   = show a
  show (And  p q) = formulaParen p ++ " ∧ " ++ formulaParen q
  show (Or   p q) = formulaParen p ++ " ∨ " ++ formulaParen q
  show (Impl p q) = formulaParen p ++ " → " ++ formulaParen q

type Label = Natural

data Tagged f a = Tag
  { label   :: Label
  , isTMove :: Bool
  , formula :: f a
  }
  deriving (Eq, Functor)

instance Show (f a) => Show (Tagged f a) where
  show (Tag l move taggedFormula) = (if move then 'T' else 'F') : show l ++ ": " ++ show taggedFormula

instance Ord (f a) => Ord (Tagged f a) where
  compare (Tag labelL moveL formulaL) (Tag labelR moveR formulaR) =
    compare (formulaL, labelL, moveL) (formulaR, labelR, moveR)

data OneRule
  = RuleTAnd
  | RuleFOr
  | RuleFImplFresh
  | RuleFImplReuse
  deriving (Eq, Ord)

instance Show OneRule where
  show RuleTAnd       = "T∧"
  show RuleFOr        = "F∨"
  show RuleFImplFresh = "F→₁"
  show RuleFImplReuse = "F→₃"

data TwoRule
  = RuleFAnd
  | RuleTOr
  | RuleTImpl
  deriving (Eq, Ord)

instance Show TwoRule where
  show RuleFAnd  = "F∧"
  show RuleTOr   = "T∨"
  show RuleTImpl = "T→"

data StageDescriptor a = SD
  { complex  :: [Tagged Formula a]
  , used     :: S.Set (Tagged Formula a)
  , atomic   :: S.Set (Tagged Atom a)
  , labelRel :: M.Map Label (S.Set Label, S.Set Label)
  , newLabel :: Label
  }
  deriving (Show, Eq)


reachableFrom :: M.Map Label (S.Set Label, S.Set Label) -> Label -> S.Set Label
reachableFrom rel start = go S.empty (children start)
  where
    children w = maybe S.empty snd (M.lookup w rel)

    go seen frontier | S.null frontier = seen
                     | otherwise       = go (S.union seen fresh) (S.unions $ S.map children fresh)
      where
        fresh = S.difference frontier seen


reachableTo :: M.Map Label (S.Set Label, S.Set Label) -> Label -> S.Set Label
reachableTo rel start = go S.empty (parents start)
  where
    parents w = maybe S.empty fst (M.lookup w rel)

    go seen frontier | S.null frontier = seen
                     | otherwise       = go (S.union seen fresh) (S.unions $ S.map parents fresh)
      where
        fresh = S.difference frontier seen


data PartialProofTree a = Zero (StageDescriptor a)
                        | One (StageDescriptor a) OneRule (PartialProofTree a)
                        | Two (StageDescriptor a) TwoRule (PartialProofTree a) (PartialProofTree a)
                        deriving (Show, Eq)

setLabel :: Natural -> Tagged f a -> Tagged f a
setLabel newLabel (Tag _ move taggedFormula) = Tag newLabel move taggedFormula

isTImpl :: Tagged Formula a -> Bool
isTImpl (Tag _ True (Impl _ _)) = True
isTImpl _                       = False

isLabelled :: Label -> Tagged f a -> Bool
isLabelled l = (== l) . label

unionBoth :: (Ord a, Ord b) => (S.Set a, S.Set b) -> (S.Set a, S.Set b) -> (S.Set a, S.Set b)
unionBoth (a0, b0) (a1, b1) = (S.union a0 a1, S.union b0 b1)

develop :: forall a. (Eq a, Ord a) => StageDescriptor a -> PartialProofTree a
develop sd@SD{..} = case complex of
  []                                      -> Zero sd
  _ | isClosed intuitionisticCondition sd -> Zero sd
  f@(Tag l move  (Atom a))   : comps -> develop $ sd { complex = comps, used = f `S.insert` used, atomic = Tag l move a `S.insert` atomic }
  f@(Tag l True  (And  p q)) : comps -> One sd RuleTAnd (develop $ sd { complex = Tag l True p : Tag l True q : comps, used = f `S.insert` used })
  f@(Tag l False (And  p q)) : comps -> Two sd RuleFAnd (develop $ sd { complex = Tag l False p : comps, used = f `S.insert` used })
                                                      (develop $ sd { complex = Tag l False q : comps, used = f `S.insert` used })
  f@(Tag l True  (Or   p q)) : comps -> Two sd RuleTOr (develop $ sd { complex = Tag l True p : comps, used = f `S.insert` used })
                                                     (develop $ sd { complex = Tag l True q : comps, used = f `S.insert` used })
  f@(Tag l False (Or   p q)) : comps -> One sd RuleFOr (develop $ sd { complex = Tag l False p : Tag l False q : comps, used = f `S.insert` used })
  f@(Tag l True  (Impl p q)) : comps -> Two sd RuleTImpl (develop $ sd { complex = Tag l False p : comps, used = f `S.insert` used })
                                                       (develop $ sd { complex = Tag l True  q : comps, used = f `S.insert` used })
  f@(Tag l False (Impl p q)) : comps
    | hasWitness                  -> develop $ sd { complex = comps, used = f `S.insert` used }
    | hasPremise && hasConseq     -> develop $ sd { complex = comps, used = f `S.insert` used }
    | hasPremise && not hasConseq -> One sd RuleFImplReuse (develop $ sd { complex = Tag l False q : comps
                                                                       , used    = f `S.insert` used
                                                                       })
    | otherwise                   -> One sd RuleFImplFresh (develop $ sd { complex  = comps'
                                                                       , used     = used''
                                                                       , atomic   = atomic'
                                                                       , labelRel = M.insertWith unionBoth l (S.empty, S.singleton newLabel)
                                                                                  $ M.insertWith unionBoth newLabel (S.singleton l, S.empty)
                                                                                    labelRel
                                                                       , newLabel = succ newLabel
                                                                       })
    where
      used' = f `S.insert` used
      usedList = S.toList used'
      formulas = comps ++ usedList

      labelGrouped :: M.Map Label [Tagged Formula a]
      labelGrouped = M.fromListWith (++) $ (label &&& pure) <$> formulas

      hasFormula :: Bool -> Formula a -> [Tagged Formula a] -> Bool
      hasFormula m form = any $ \tf -> isTMove tf == m && formula tf == form

      isWitness :: [Tagged Formula a] -> Bool
      isWitness = liftA2 (&&) (hasFormula True p) (hasFormula False q)

      descendants = l `S.insert` reachableFrom labelRel l
      ancestors   = l `S.insert` reachableTo   labelRel l

      hasWitness = any isWitness $ M.elems $ M.filterWithKey (\l' _ -> l' `S.member` descendants) labelGrouped
      hasPremise = hasFormula True  p $ concat $ M.elems $ M.filterWithKey (\l' _ -> l' `S.member` ancestors) labelGrouped
      hasConseq  = hasFormula False q $ concat $ l `M.lookup` labelGrouped

      inheritedTComps = setLabel newLabel <$> filter (liftA2 (&&) isTMove (isLabelled l)) comps
      inheritedTAtoms = S.map (setLabel newLabel) $ S.filter (liftA2 (&&) isTMove (isLabelled l)) atomic
      inheritedTUsed = S.fromList $ setLabel newLabel <$> filter (liftA2 (&&) isTMove (isLabelled l)) usedList
      inheritedTImpls = setLabel newLabel <$> filter (liftA2 (&&) isTImpl (isLabelled l)) usedList

      comps' = Tag newLabel True p : Tag newLabel False q : inheritedTComps ++ comps ++ inheritedTImpls
      atomic' = inheritedTAtoms `S.union` atomic
      used'' = inheritedTUsed `S.union` used'


initStage :: Formula a -> StageDescriptor a
initStage p = SD { complex  = [Tag l False p]
                 , used     = S.empty
                 , atomic   = S.empty
                 , labelRel = M.empty
                 , newLabel = succ l
                 }
                 where
                   l = 0

intuitionisticCondition :: Eq a => Tagged Atom a -> Tagged Atom a -> Bool
intuitionisticCondition (Tag labelL _ atomL) (Tag labelR _ atomR) = labelL == labelR && atomL == atomR

classicalCondition :: Eq a => Tagged Atom a -> Tagged Atom a -> Bool
classicalCondition (Tag _ _ atomL) (Tag _ _ atomR) = atomL == atomR


isClosed :: (Eq a, Ord a) => (Tagged Atom a -> Tagged Atom a -> Bool) -> StageDescriptor a -> Bool
isClosed group SD{..} = hasTBot || hasFTop || hasContradiction
  where
    hasTBot = any isTBot atomic
    hasFTop = any isFTop atomic

    isTBot (Tag _ True Bot) = True
    isTBot _                = False

    isFTop (Tag _ False Top) = True
    isFTop _                 = False

    hasContradiction = any ((> 1) . length) $ groupBy group $ S.toAscList atomic


allBranches :: PartialProofTree a -> [StageDescriptor a]
allBranches (Zero a)      = [a]
allBranches (One _ _ x)   = allBranches x
allBranches (Two _ _ l r) = allBranches l ++ allBranches r

prettySD' :: Show a => StageDescriptor a -> (Int, [String])
prettySD' SD{..} = (maximum (0 : fmap length stageLines), stageLines)
 where
  stageLines = fmap show complex ++ fmap show (S.toAscList atomic)

indent :: Int -> [String] -> [String]
indent width = fmap ((++) $ replicate width ' ')

appendAligned :: Int -> String -> String -> String
appendAligned width left right = left ++ replicate (max 0 $ width - length left) ' ' ++ right

alignLines :: [String] -> [String] -> ([String], [String])
alignLines leftLines rightLines
  | length leftLines <= length rightLines =
      (leftLines ++ replicate (length rightLines - length leftLines) "", rightLines)
  | otherwise =
      (leftLines, rightLines ++ replicate (length leftLines - length rightLines) "")


prettyPPT' :: Show a => PartialProofTree a -> (Int, (Int, [String]))
prettyPPT' (Zero sd) = (0, prettySD' sd)
prettyPPT' (One sd rule ppt) = (rootOffset, (width, indent rootOffset stageLines ++ line : subtreeLines))
  where
    (rootOffset, (subtreeWidth, subtreeLines)) = prettyPPT' ppt
    (stageWidth, stageLines) = prettySD' sd
    ruleName = show rule
    ruleWidth = length ruleName
    width = maximum [rootOffset + stageWidth, subtreeWidth, 4 + ruleWidth]
    line = replicate (width - ruleWidth - 1) '-' ++ ' ' : ruleName
prettyPPT' (Two sd rule pptl pptr) =
  ( rootOffset
  , (width , indent rootOffset stageLines ++ line : zipWith (appendAligned rightOffset) leftLines' rightLines')
  )
  where
    sepBase = 4
    (_, (leftWidth, leftLines)) = prettyPPT' pptl
    (_, (rightWidth, rightLines)) = prettyPPT' pptr
    (stageWidth, stageLines) = prettySD' sd
    center' = (leftWidth + sepBase + rightWidth) `div` 2
    sep = sepBase + if (center' `mod` 2) == (stageWidth `mod` 2) then 0 else 1
    center = (leftWidth + sep + rightWidth) `div` 2
    rootOffset = max 0 (center - (stageWidth `div` 2))
    rightOffset= leftWidth + sep
    ruleName = show rule
    ruleWidth = length ruleName
    width = maximum [rootOffset + stageWidth, rightOffset + rightWidth, ruleWidth]
    line = replicate (width - ruleWidth - 1) '-' ++ ' ' : ruleName
    (leftLines', rightLines') = alignLines leftLines rightLines


prettyPPT :: Show a => PartialProofTree a -> String
prettyPPT = intercalate "\n" . fmap trimRight . snd . snd . prettyPPT'
  where
    trimRight = reverse . dropWhile isSpace . reverse

summary :: (Show a, Eq a, Ord a) => Formula a -> IO ()
summary form = do
  let proofTree = develop $ initStage form
  putStrLn $ prettyPPT proofTree
  putStrLn "=================================================="
  putStrLn $ "intuitionistic tautology: " ++ show (all (isClosed intuitionisticCondition) $ allBranches proofTree)
  putStrLn $ "classical tautology     : " ++ show (all (isClosed classicalCondition)      $ allBranches proofTree)

topKeywords :: [String]
topKeywords = [ "Top"
              , "top"
              , "T"
              , "⊤"
              ]

botKeywords :: [String]
botKeywords = [ "Bot"
              , "bot"
              , "F"
              , "⊥"
              ]

notKeywords :: [String]
notKeywords = [ "Not"
              , "not"
              , "!"
              , "~"
              , "¬"
              ]

andKeywords :: [String]
andKeywords = [ "And"
              , "and"
              , "*"
              , "&"
              , "&&"
              , "∧"
              ]

orKeywords :: [String]
orKeywords = [ "Or"
             , "or"
             , "+"
             , "|"
             , "||"
             , "∨"
             ]

implKeywords :: [String]
implKeywords = [ "Impl"
               , "impl"
               , "->"
               , "=>"
               , "→"
               , "⇒"
               , "⊃"
               ]

keywords :: [String]
keywords = concat [ topKeywords
                  , botKeywords
                  , notKeywords
                  , andKeywords
                  , orKeywords
                  , implKeywords
                  ]

lexeme :: P.ReadP a -> P.ReadP a
lexeme p = p <* P.skipSpaces

parserKeywords :: [String] -> P.ReadP String
parserKeywords keywordList = lexeme $ P.choice (fmap P.string keywordList) <* boundary
  where
    boundary = do
      rest <- P.look
      case rest of
        []      -> return ()
        (')':_) -> return ()
        (c  :_) -> guard $ isSpace c

parserIdentifier :: P.ReadP String
parserIdentifier = lexeme $ do
  name <- P.munch1 $ \c -> not (isSpace c || c == '(' || c == ')')
  if name `elem` keywords
    then P.pfail
    else return name

parserAtom :: P.ReadP (Atom String)
parserAtom = do
  P.choice [ parserKeywords topKeywords >> return Top
           , parserKeywords botKeywords >> return Bot
           , Pure <$> parserIdentifier
           ]

parserArgument :: P.ReadP (Formula String)
parserArgument = P.between (lexeme $ P.char '(') (lexeme $ P.char ')') parserFormula P.<++ (Atom <$> parserAtom)

parserNot :: P.ReadP (Formula String)
parserNot = (parserKeywords notKeywords >> fmap (flip Impl $ Atom Bot) parserNot) P.<++ parserArgument

parserAnd :: P.ReadP (Formula String)
parserAnd = P.chainl1 parserNot $ And <$ parserKeywords andKeywords

parserOr :: P.ReadP (Formula String)
parserOr = P.chainl1 parserAnd $ Or <$ parserKeywords orKeywords

parserImpl :: P.ReadP (Formula String)
parserImpl = P.chainr1 parserOr $ Impl <$ parserKeywords implKeywords

parserFormula :: P.ReadP (Formula String)
parserFormula = parserImpl

parse :: P.ReadP a -> String -> [a]
parse parser = fmap fst . P.readP_to_S (P.skipSpaces *> parser <* P.skipSpaces <* P.eof)

main :: IO ()
main = do
  args <- getArgs
  let maybeFormula = listToMaybe args >>= listToMaybe . parse parserFormula
  maybe (return ()) summary maybeFormula
