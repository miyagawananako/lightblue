#!/bin/bash

# collectTypeCheckTreesを実行してからjsem-train-evalを実行するスクリプト

set -e  # エラーで停止

# デフォルト値
JSEM_DIR="${1:-../JSeM/data/v1.0}"
OUTPUT_PATH="${2:-jsemTypeCheckTreeData}"
BI_DIRECTIONAL="${3:-False}"
EMB_DIM="${4:-256}"
HIDDEN_SIZE="${5:-256}"
LAYERS="${6:-1}"
BIAS="${7:-False}"
LR="${8:-5.0e-4}"
BATCH_SIZE="${9:-32}"
EPOCHS="${10:-10}"
MAX_DEPTH="${11:-9}"
MAX_TIME="${12:-6000}"

echo "=========================================="
echo "Starting collectTypeCheckTrees..."
echo "=========================================="
echo "  jsemDir: $JSEM_DIR"
echo "  outputPath: $OUTPUT_PATH"
echo "=========================================="
stack run collectTypeCheckTrees-exe -- "$JSEM_DIR" "$OUTPUT_PATH"

echo ""
echo "=========================================="
echo "collectTypeCheckTrees completed successfully!"
echo "=========================================="
echo ""

# maxTimeの異なる値でそれぞれ実行
MAX_TIMES=(30000 60000 90000)

for MAX_TIME_VALUE in "${MAX_TIMES[@]}"; do
  echo "=========================================="
  echo "Starting jsem-train-eval with maxTime=$MAX_TIME_VALUE..."
  echo "=========================================="
  echo "  jsemDataPath: $OUTPUT_PATH"
  echo "  biDirectional: $BI_DIRECTIONAL"
  echo "  embDim: $EMB_DIM"
  echo "  hiddenSize: $HIDDEN_SIZE"
  echo "  layers: $LAYERS"
  echo "  bias: $BIAS"
  echo "  lr: $LR"
  echo "  batchSize: $BATCH_SIZE"
  echo "  epochs: $EPOCHS"
  echo "  maxDepth: $MAX_DEPTH"
  echo "  maxTime: $MAX_TIME_VALUE"
  echo "=========================================="
  stack run jsem-train-eval-exe -- "$OUTPUT_PATH" "$BI_DIRECTIONAL" "$EMB_DIM" "$HIDDEN_SIZE" "$LAYERS" "$BIAS" "$LR" "$BATCH_SIZE" "$EPOCHS" "$MAX_DEPTH" "$MAX_TIME_VALUE"
  
  echo ""
  echo "=========================================="
  echo "jsem-train-eval (maxTime=$MAX_TIME_VALUE) completed successfully!"
  echo "=========================================="
  echo ""
done

echo "=========================================="
echo "All jsem-train-eval runs completed successfully!"
echo "=========================================="
