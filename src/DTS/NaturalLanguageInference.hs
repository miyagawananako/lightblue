{-# LANGUAGE RecordWildCards, DuplicateRecordFields #-}

{-|
Module      : DTS.NaturalLanguageInference
Copyright   : Daisuke Bekki
Licence     : All right reserved
Maintainer  : Daisuke Bekki <bekki@is.ocha.ac.jp>
Stability   : beta

A module for Natural Language Inference 
-}

module DTS.NaturalLanguageInference (
  InferenceSetting(..)
  --, InferencePair(..)
  --, InferenceResult(..)
  , ProverName(..)
  , getProver
  , ParseResult(..)
  , ParseTreeAndFelicityChecks(..)
  , QueryAndDiagrams(..)
  , parseWithTypeCheck
  , trawlParseResult
  -- RTE API (自然言語用)
  , RTEResult(..)
  , runRTE
  -- RTE API (Preterm用)
  , RTEPretermResult(..)
  , runRTEWithPreterms
  ) where

import Control.Monad (join)    --base
import Control.Monad.State (lift)         --mtl
import Control.Monad.IO.Class (liftIO)    --base
import Control.Applicative ((<|>))        --base
import Control.Parallel (par,pseq)        --base
import qualified System.IO as S           --base
import qualified Data.Char as C           --base
import qualified Data.Text.Lazy as T      --text
import qualified Data.Text.Lazy.IO as T   --text
import qualified Data.List as L           --base
import ListT (ListT(..),fromFoldable,toReverseList,toList,take,null,uncons,cons) --list-t
import qualified Parser.ChartParser as CP      --lightblue
import qualified Parser.PartialParsing as Partial --lightblue
import qualified Parser.CCG as CCG             --lightblue
import Interface.Tree as Tree                  --lightblue
--import Parser.Language (LangOptions(..),jpOptions)
import qualified DTS.UDTTdeBruijn as UDTT      --lightblue
import qualified DTS.DTTdeBruijn as DTT        --lightblue
import qualified DTS.QueryTypes as QT          --lightblue
import qualified DTS.TypeChecker as TY         --lightblue
import qualified DTS.Prover.Wani.Prove as Wani --lightblue
import qualified JSeM as JSeM                  --jsem

data InferenceSetting = InferenceSetting {
  beam :: Int     -- ^ beam width
  , maxDepth :: Maybe Int -- ^ max depth for prover
  , maxTime :: Maybe Int  -- ^ max time for prover
  , parseSetting :: CP.ParseSetting
  , typeChecker :: QT.TypeChecker
  , proverName :: ProverName
  } 

type InferenceLabel = JSeM.YesNo
--data InferenceLabel = YES | NO | UNK deriving (Eq, Show, Read)

-- data InferencePair = InferencePair {
--   premises :: [T.Text]   -- ^ premises
--   , hypothesis :: T.Text -- ^ a hypothesis
--   } deriving (Eq, Show)

--data InferenceResult = InferenceResult (InferencePair, [CCG.Node], [UDTT.Preterm], DTT.Signature, [Tree QT.DTTrule DTT.Judgment]) --, QT.ProofSearchQuery, QT.ProofSearchResult)) 

data ProverName = Wani | Null deriving (Eq,Show)

instance Read ProverName where
  readsPrec _ r =
    [(Wani,s) | (x,s) <- lex r, map C.toLower x == "wani"]
    ++ [(Null,s) | (x,s) <- lex r, map C.toLower x == "null"]
    -- ++ [(Diag,s) | (x,s) <- lex r, map C.toLower x == "diag"]
    -- ++ [(Coq,s) | (x,s) <- lex r, map C.toLower x == "coq"]

getProver :: ProverName -> QT.ProverBuilder
getProver pn = case pn of
  Wani -> Wani.prove'
  Null -> TY.nullProver

{-- Data structure for sequential parsing and the inference --} 

data ParseResult = 
  SentenceAndParseTrees T.Text (ListT IO ParseTreeAndFelicityChecks) -- ^ A next sentence and its parse results
  | InferenceResults QueryAndDiagrams QueryAndDiagrams 
  | NoSentence 
data ParseTreeAndFelicityChecks = 
  ParseTreeAndFelicityChecks CCG.Node DTT.Signature UDTT.TypeCheckQuery (ListT IO (QT.DTTProofDiagram, ParseResult)) 
  -- ^ A parse result, type check query for its felicity condition, and its results
  -- ^ A type check diagram and the next sentence if this is not the last sentence, or an inference query otherwise.
data QueryAndDiagrams = 
  QueryAndDiagrams DTT.ProofSearchQuery (ListT IO QT.DTTProofDiagram) 
  -- ^ A proof search query for the inference and its results.

-- | Parse sequential texts, and check their semantic felicity condition.
-- | If noInference = True, it does not execute inference.
-- | The specification of this function reflects a view about what are entailments between texts,          
-- | that is an interface problem between natural language semantics and logic
parseWithTypeCheck :: CP.ParseSetting -> QT.Prover -> DTT.Signature -> DTT.Context -> [T.Text] -> ParseResult
parseWithTypeCheck ps prover signtr contxt txts =
  let nodes = sequentialParsing ps txts
  in sequentialTypeCheck ps prover signtr contxt nodes
  
type Discourse = [(T.Text, ListT IO CCG.Node)]

sequentialParsing :: CP.ParseSetting -> [T.Text] -> Discourse
sequentialParsing ps txts = 
  parallelFor txts $ \txt -> (txt, takeNbest (CP.nParse ps) $ join $ fmap fromFoldable $ lift $ Partial.simpleParse ps txt)
    -- | T.Text =simpleParse=>    IO [CCG.Node]
    -- |        =lift=>           ListT IO [CCG.node] 
    -- |        =fmap(foldable)=> ListT IO (ListT IO CCG.Node)
    -- |        =join=>           ListT IO CCG.Node
    -- |        =takeNbest Int => ListT IO CCG.Node

sequentialTypeCheck :: CP.ParseSetting -> QT.Prover -> DTT.Signature -> DTT.Context -> Discourse -> ParseResult
sequentialTypeCheck _ _ _ [] [] = NoSentence     -- ^ Context is empty and no sentece is given 
sequentialTypeCheck ps prover signtr (typ:contxt) [] = -- ^ Context is given and no more sentence (= All parse done)
  if CP.noInference ps
    then NoSentence
    else let (qadPos, qadNeg) = runInferenceCore prover (CP.nProof ps) signtr contxt typ
         in InferenceResults qadPos qadNeg
sequentialTypeCheck ps prover signtr contxt ((text,nodes):rests) = 
  SentenceAndParseTrees text $ 
    parallelM nodes $ \node -> 
         let signtr' = L.nub $ (CCG.sig node) ++ signtr
             tcQueryType = UDTT.Judgment signtr' contxt (CCG.sem node) DTT.Type
             tcQueryKind = UDTT.Judgment signtr' contxt (CCG.sem node) DTT.Kind
         in ParseTreeAndFelicityChecks node signtr' tcQueryType $ 
              let tcDiagrams = takeNbest (CP.nTypeCheck ps) $ (TY.typeCheck prover (CP.verbose ps) tcQueryType)
                                                              <|> (TY.typeCheck prover (CP.verbose ps) tcQueryKind)
              in parallelM tcDiagrams $ \tcDiagram -> 
                   let contxt' = (DTT.trm $ Tree.node tcDiagram):contxt
                   in (tcDiagram, sequentialTypeCheck ps prover signtr' contxt' rests)

-- | Take n element from the top of the list.
-- | If n < 0, it returns all the elements.
takeNbest :: Int -> ListT IO a -> ListT IO a
takeNbest n l
  | n >= 0 = ListT.take n l
  | otherwise = l

{-- Core inference logic (共通の推論ロジック) --}

-- | 推論クエリを作成し、証明探索を実行する（共通ヘルパー関数）
-- | sequentialTypeCheck と runRTEWithPreterms の両方から使用される
runInferenceCore :: QT.Prover         -- ^ 証明器
                 -> Int               -- ^ 証明の最大数 (-1で無制限)
                 -> DTT.Signature     -- ^ シグネチャ
                 -> DTT.Context       -- ^ コンテキスト（前提）
                 -> DTT.Preterm       -- ^ 仮説
                 -> (QueryAndDiagrams, QueryAndDiagrams)
runInferenceCore prover nProof signtr contxt hypothesis =
  let psqPos = DTT.ProofSearchQuery signtr contxt hypothesis
      resultPos = takeNbest nProof $ prover psqPos
      psqNeg = DTT.ProofSearchQuery signtr contxt (DTT.Pi hypothesis DTT.Bot)
      resultNeg = takeNbest nProof $ prover psqNeg
  in (QueryAndDiagrams psqPos resultPos, QueryAndDiagrams psqNeg resultNeg)
 
{-- Trawling functions --}

trawlParseResult :: ParseResult -> ListT IO InferenceLabel
trawlParseResult (SentenceAndParseTrees _ parseTreeAndFelicityChecks) = do
  (ParseTreeAndFelicityChecks _ _ _ felicityCheckAndMores) <- parseTreeAndFelicityChecks 
  (_, parseResult) <- felicityCheckAndMores
  label <- trawlParseResult parseResult
  return label
trawlParseResult (InferenceResults (QueryAndDiagrams _ resultPos) (QueryAndDiagrams _ resultNeg)) = do
  ifYes <- liftIO $ ListT.null resultPos
  ifNo  <- liftIO $ ListT.null resultNeg
  return $ case () of
             _ | not ifYes -> JSeM.Yes
               | not ifNo  -> JSeM.No
               | otherwise -> JSeM.Unk
trawlParseResult NoSentence = fromFoldable []

{-- Parallel processing --}

parallelM :: ListT IO a -> (a -> b) -> ListT IO b
parallelM lst f = join $ lift $ do
  unc <- uncons lst -- Maybe (a, ListT IO a)
  case unc of
    Nothing -> return $ fromFoldable []
    Just (x,mxs) -> return $ fx `par` mfxs `pseq` (cons fx mfxs)
                    where fx   = f x
                          mfxs = parallelM mxs f

parallelFor :: [a] -> (a -> b) -> [b]
parallelFor [] f = []
parallelFor (x:xs) f = fx `par` fxs `pseq` (fx:fxs)
  where fx = f x
        fxs = parallelFor xs f

{-- RTE (Recognizing Textual Entailment) API --}

-- | RTEの結果を表すデータ型
data RTEResult = RTEResult {
  rteLabel :: JSeM.YesNo,        -- ^ 推論ラベル (Yes/No/Unk/Other)
  rteParseResult :: ParseResult  -- ^ パース結果（詳細情報が必要な場合用）
  }

-- | RTEを実行する
-- | 前提文のリストと仮説文を受け取り、推論ラベルとパース結果を返す
-- | 
-- | 使用例:
-- | @
-- | let signature = [("dummy", DTT.Entity)]
-- |     context = []
-- | result <- runRTE parseSetting prover signature context ["太郎は学生だ", "学生は人間だ"] "太郎は人間だ"
-- | print $ rteLabel result  -- Yes/No/Unk/Other
-- | @
runRTE :: CP.ParseSetting     -- ^ パース設定
       -> QT.Prover           -- ^ 証明器
       -> DTT.Signature       -- ^ 初期シグネチャ（通常は [("dummy", DTT.Entity)]）
       -> DTT.Context         -- ^ 初期コンテキスト（通常は []）
       -> [T.Text]            -- ^ 前提文のリスト
       -> T.Text              -- ^ 仮説文
       -> IO RTEResult
runRTE parseSetting prover signature context premises hypothesis = do
  let sentences = premises ++ [hypothesis]
      parseResult = parseWithTypeCheck parseSetting prover signature context sentences
  inferenceLabels <- toList $ trawlParseResult parseResult
  let prediction = case inferenceLabels of
        [] -> JSeM.Other
        (bestLabel:_) -> bestLabel
  return $ RTEResult prediction parseResult

{-- RTE API for Preterm (自然言語パースをスキップ) --}

-- | Preterm形式でのRTE結果を表すデータ型
data RTEPretermResult = RTEPretermResult {
  rtePretermLabel :: JSeM.YesNo,                              -- ^ 推論ラベル (Yes/No/Unk)
  rtePretermQueryPos :: DTT.ProofSearchQuery,                 -- ^ 肯定の証明クエリ
  rtePretermQueryNeg :: DTT.ProofSearchQuery,                 -- ^ 否定の証明クエリ
  rtePretermProofsPos :: [QT.DTTProofDiagram],                -- ^ 肯定の証明図
  rtePretermProofsNeg :: [QT.DTTProofDiagram]                 -- ^ 否定の証明図
  }

-- | Preterm形式でRTEを実行する
-- | 自然言語のパースをスキップして、直接DTT.Pretermの形で前提と仮説を受け取る
-- | 
-- | 使用例:
-- | @
-- | let signature = [("human", DTT.Pi DTT.Entity DTT.Type), ("student", DTT.Pi DTT.Entity DTT.Type)]
-- |     -- 前提: ∀x. student(x) → human(x)
-- |     premise = DTT.Pi (DTT.App (DTT.Con "student") (DTT.Var 0)) 
-- |                      (DTT.App (DTT.Con "human") (DTT.Var 1))
-- |     -- 仮説: student(taro) → human(taro)
-- |     hypothesis = DTT.Pi (DTT.App (DTT.Con "student") (DTT.Con "taro"))
-- |                         (DTT.App (DTT.Con "human") (DTT.Con "taro"))
-- | result <- runRTEWithPreterms prover signature [premise] hypothesis (-1)
-- | print $ rtePretermLabel result  -- Yes/No/Unk
-- | @
runRTEWithPreterms :: QT.Prover         -- ^ 証明器
                   -> DTT.Signature     -- ^ シグネチャ（定数の型宣言）
                   -> [DTT.Preterm]     -- ^ 前提のリスト（Context）
                   -> DTT.Preterm       -- ^ 仮説
                   -> Int               -- ^ 証明の最大数 (-1で無制限)
                   -> IO RTEPretermResult
runRTEWithPreterms prover signature premises hypothesis nProof = do
  -- 共通の推論ロジックを使用
  let (QueryAndDiagrams psqPos resultPosListT, QueryAndDiagrams psqNeg resultNegListT) =
        runInferenceCore prover nProof signature premises hypothesis
  -- 証明探索を実行（遅延評価を即時評価に変換）
  proofsPos <- toList resultPosListT
  proofsNeg <- toList resultNegListT
  -- 推論ラベルを決定
  let label = case () of
        _ | not (Prelude.null proofsPos) -> JSeM.Yes  -- 肯定の証明が見つかった
          | not (Prelude.null proofsNeg) -> JSeM.No   -- 否定の証明が見つかった
          | otherwise                    -> JSeM.Unk -- どちらも見つからない
  return $ RTEPretermResult label psqPos psqNeg proofsPos proofsNeg