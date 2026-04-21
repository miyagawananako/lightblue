#!/bin/bash

# collectTypeCheckTreesを実行してからjsem-train-evalを実行するスクリプト
# ループ順は元スクリプトの逆順にしている

# set -e は使わず、個々の失敗を記録して継続する

# デフォルト値
JSEM_DIR="${1:-../JSeM/data/v1.0}"
OUTPUT_PATH="${2:-jsemTypeCheckTreeData}"
BI_DIRECTIONAL_VALUES=(${3:-True False})
EMB_DIM_VALUES=(${4:-256 128})
LAYERS_VALUES=(${5:-2 1})
BIAS="${6:-True}"
LR="${7:-5.0e-4}"
BATCH_SIZE="${8:-32}"
EPOCHS="${9:-10}"
MAX_DEPTH="${10:-9}"
THRESHOLD_VALUES=(${11:-2000})

for THRESH in "${THRESHOLD_VALUES[@]}"; do
  for LAYERS in "${LAYERS_VALUES[@]}"; do
    for EMB_DIM in "${EMB_DIM_VALUES[@]}"; do
      for BI_DIRECTIONAL in "${BI_DIRECTIONAL_VALUES[@]}"; do
        echo "=========================================="
        echo "Starting jsem-train-eval with hyperparams..."
        echo "=========================================="
        echo "  jsemDataPath: $OUTPUT_PATH"
        echo "  biDirectional: $BI_DIRECTIONAL"
        echo "  embDim: $EMB_DIM"
        echo "  hiddenSize: $EMB_DIM"
        echo "  layers: $LAYERS"
        echo "  bias: $BIAS"
        echo "  lr: $LR"
        echo "  batchSize: $BATCH_SIZE"
        echo "  epochs: $EPOCHS"
        echo "  maxDepth: $MAX_DEPTH"
        echo "  threshold: $THRESH"
        echo "=========================================="
        if ! stack run jsem-train-eval-exe -- "$OUTPUT_PATH" "$BI_DIRECTIONAL" "$EMB_DIM" "$EMB_DIM" "$LAYERS" "$BIAS" "$LR" "$BATCH_SIZE" "$EPOCHS" "$MAX_DEPTH" "$THRESH"; then
          echo "=========================================="
          echo "jsem-train-eval failed. Continuing..."
          echo "=========================================="
        fi

        echo ""
        echo "=========================================="
        echo "jsem-train-eval completed successfully!"
        echo "=========================================="
        echo ""
      done
    done
  done
done

echo "=========================================="
echo "All jsem-train-eval runs completed successfully!"
echo "=========================================="
