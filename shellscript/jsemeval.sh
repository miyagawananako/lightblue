#!/bin/bash

# set -e は使わず、個々の失敗を記録して継続する

# デフォルト値
JSEM_DIR="${1:-../JSeM/data/v1.0}"
OUTPUT_PATH="${2:-jsemTypeCheckTreeData}"
BI_DIRECTIONAL_VALUES="${3:-False}"
EMB_DIM_VALUES="${4:-128}"
LAYERS_VALUES="${5:-1}"
BIAS="${6:-True}"
LR="${7:-5.0e-4}"
BATCH_SIZE="${8:-32}"
EPOCHS="${9:-10}"
MAX_DEPTH="${10:-9}"
THRESHOLD="${11:-2000}"
TOP_K_VALUES=("4" "5" "6" "7" "8" "9" "3")

for BI_DIRECTIONAL in "${BI_DIRECTIONAL_VALUES[@]}"; do
  for EMB_DIM in "${EMB_DIM_VALUES[@]}"; do
    for LAYERS in "${LAYERS_VALUES[@]}"; do
      for THRESH in "${THRESHOLD[@]}"; do
        for TOP_K in "${TOP_K_VALUES[@]}"; do
          if [ -z "$TOP_K" ]; then
            TOP_K_DISPLAY="(not specified)"
          else
            TOP_K_DISPLAY="$TOP_K"
          fi

          echo "=========================================="
          echo "Starting jsem-eval with hyperparams..."
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
          echo "  topK: $TOP_K_DISPLAY"
          echo "=========================================="
          if [ -z "$TOP_K" ]; then
            if ! stack run jsem-train-eval-exe -- "$OUTPUT_PATH" "$BI_DIRECTIONAL" "$EMB_DIM" "$EMB_DIM" "$LAYERS" "$BIAS" "$LR" "$BATCH_SIZE" "$EPOCHS" "$MAX_DEPTH" "$THRESH"; then
              echo "=========================================="
              echo "jsem-train-eval failed. Continuing..."
              echo "=========================================="
            fi
          else
            if ! stack run jsem-train-eval-exe -- "$OUTPUT_PATH" "$BI_DIRECTIONAL" "$EMB_DIM" "$EMB_DIM" "$LAYERS" "$BIAS" "$LR" "$BATCH_SIZE" "$EPOCHS" "$MAX_DEPTH" "$THRESH" "$TOP_K"; then
              echo "=========================================="
              echo "jsem-train-eval failed. Continuing..."
              echo "=========================================="
            fi
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
done

echo "=========================================="
echo "All jsem-train-eval runs completed successfully!"
echo "=========================================="
