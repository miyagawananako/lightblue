module NeuralWani.Builder
  ( neuralWaniBuilder
  , modelPath
  , frequentWordsPath
  ) where

import qualified DTS.Prover.Wani.WaniBase as WB
import qualified DTS.Prover.Wani.BackwardRules as BR
import qualified DTS.Prover.Wani.Arrowterm as A
import qualified DTS.QueryTypes as QT

import qualified Data.Text.Lazy as T
import qualified Data.ByteString as B --bytestring
import Data.Store (decode)

import Torch.Serialize (loadParams)
import Torch.NN (sample)
import Torch.Device (Device(..),DeviceType(..))

import qualified NeuralWani.Forward as F
import qualified NeuralWani.SplitJudgment as S
import qualified Data.Map.Strict as Map

-- 本来lightblue内に置くパス（パスは仮）。CUDA でしか開けない
modelPath :: FilePath
modelPath = "trainedDataBackwardWithoutF/typeEo_biFalse_s32_lr5.0e-4_i128_h128_layer1/2025-12-16_13-41-38/seq-class.model"
frequentWordsPath :: FilePath
frequentWordsPath = "trainedDataBackwardWithoutF/typeEo_biFalse_s32_lr5.0e-4_i128_h128_layer1/2025-12-16_13-41-38/frequentWords.bin"

-- CPU用のパス
-- modelPath :: FilePath
-- modelPath = "trainedDataBackwardWithoutF/typeUnused_biFalse_s32_lr5.0e-4_i256_h256_layer1/2025-12-15_12-14-54/seq-class.model"
-- frequentWordsPath :: FilePath
-- frequentWordsPath = "trainedDataBackwardWithoutF/typeUnused_biFalse_s32_lr5.0e-4_i256_h256_layer1/2025-12-15_12-14-54/frequentWords.bin"


-- lightblue内に置く関数
neuralWaniBuilder :: IO (WB.Goal -> [BR.RuleLabel] -> [BR.RuleLabel])
neuralWaniBuilder = do
  let device = Device CUDA 0
      bi_directional = False
      hyperParams = F.HypParams
        { F.dev = device
        , F.bi_directional = bi_directional
        , F.emb_dim = 128
        , F.has_bias = True  -- 訓練時と同じ値に設定
        , F.proj_size = Nothing
        , F.vocab_size = length (enumFrom minBound :: [S.Token])
        , F.num_layers = 1
        , F.hidden_size = 128
        , F.num_rules = length (enumFrom minBound :: [BR.RuleLabel])
        }
      delimiterToken = S.Eo
  emptyModel <- sample hyperParams
  model <- loadParams emptyModel modelPath
  frequentWordsEither <- decode <$> B.readFile frequentWordsPath
  frequentWords <- case frequentWordsEither of
    Left err -> error $ "Failed to decode frequentWords: " ++ show err
    Right ws -> return ws
  -- 頻出語リストをMapに事前変換（高速化のため）
  let wordMap = S.buildWordMap frequentWords
  return $ \goal availableRuleLabels ->
    let maybeJudgment = WB.goal2NeuralWaniJudgement goal
    in case maybeJudgment of
      Just judgment ->
        let predictedRuleLabels = F.predictRule device model judgment bi_directional wordMap delimiterToken
            filteredRuleLabels = filter (`elem` availableRuleLabels) predictedRuleLabels
        in filteredRuleLabels
      Nothing -> availableRuleLabels
