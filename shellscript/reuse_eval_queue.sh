#!/bin/bash

# 4/29〜6/2 の総当たり実験 (jsemtypecheck.sh) で、並列モードのせいで評価が
# 止まったモデルを --reuse で逐次評価し直すスクリプト。
# 元の実験 (2/19) と同じく逐次 (--sequential) で測り、NeuralWani のキャッシュは
# 問題ごとに空にする (--cachescope problem) のと、時間制限ごとに空にする
# (--cachescope timelimit) のを比べる。
# どちらでも時間制限どうしは独立するので、まず全設定を両方の条件の T30000 だけで
# 評価し、最後に問題ごとの T60000 と T90000 を評価する。途中で止まっても、
# そこまでの T30000 は全設定分そろう。
# 設定ごとの評価の前に、2/19 のモデルで可視化用の探索ログを取る。
# 引数に PID を渡すと、そのプロセスの終了を待ってから始める。

WAIT_PID="$1"
R=jsemResults
DATA=jsemTypeCheckTreeData
COMMON="True 5.0e-4 32 10 9 2000"   # bias lr batchSize epochs maxDepth threshold
OPTS="--sequential --cachescope problem"

if [ -n "$WAIT_PID" ]; then
  echo "Waiting for PID $WAIT_PID to finish..."
  while kill -0 "$WAIT_PID" 2>/dev/null; do sleep 60; done
fi

# 学習済みモデルを再利用するもの: "再利用フォルダ bi emb layers"
REUSE_RUNS=(
  "$R/jsem_biFalse_s32_lr5.0e-4_i128_h128_layer1/2026-05-20_05-35-14/topk_nothing False 128 1"
  "$R/jsem_biFalse_s32_lr5.0e-4_i128_h128_layer2/2026-05-21_15-59-07/topk_nothing False 128 2"
  "$R/jsem_biFalse_s32_lr5.0e-4_i256_h256_layer1/2026-05-22_12-12-59/topk_nothing False 256 1"
  "$R/jsem_biFalse_s32_lr5.0e-4_i256_h256_layer2/2026-05-23_20-20-44/topk_nothing False 256 2"
  "$R/jsem_biFalse_s32_lr5.0e-4_i512_h512_layer1/2026-05-24_15-14-42/topk_nothing False 512 1"
  "$R/jsem_biFalse_s32_lr5.0e-4_i512_h512_layer2/2026-05-26_01-22-57/topk_nothing False 512 2"
  "$R/jsem_biTrue_s32_lr5.0e-4_i128_h128_layer1/2026-05-28_21-30-38/topk_nothing True 128 1"
  "$R/jsem_biTrue_s32_lr5.0e-4_i128_h128_layer2/2026-05-31_13-19-43/topk_nothing True 128 2"
  "$R/jsem_biTrue_s32_lr5.0e-4_i256_h256_layer1/2026-06-01_23-56-23/topk_nothing True 256 1"
  "$R/jsem_biTrue_s32_lr5.0e-4_i256_h256_layer2/2026-05-13_04-00-20/topk_nothing True 256 2"
)

mkdir -p logs

# run <log name> <jsem-train-eval-exe args...>
run() {
  local LOG="logs/$1_$(date +%Y-%m-%d_%H-%M-%S).log"
  LAST_LOG="$LOG"
  shift
  echo "=== $* -> $LOG"
  if ! stack exec jsem-train-eval-exe -- "$@" > "$LOG" 2>&1; then
    echo "failed: $* (continuing)"
  fi
}

# --- 可視化用の探索ログ: 2/19 のモデル、T30000 / T60000 / T90000 ---
# 考察の中心の 2/19 のモデルなので、ほかの設定の評価より先に取る。
# ログの書き出しは計測に影響するので、時間はここでは比べない。1問で 1〜3GB に
# なるので、時間制限ごとにディスクの空きを確かめ、足りなければ飛ばす。
for T in 30000 60000 90000; do
  FREE_GB=$(df -BG --output=avail . | tail -1 | tr -dc '0-9')
  if [ "$FREE_GB" -lt 200 ]; then
    echo "skipped: search log run T$T needs 200GB free, only ${FREE_GB}GB"
    continue
  fi
  run "searchlog_2026-02-19model_T$T" \
      --reuse "$R/jsem_biFalse_s32_lr5.0e-4_i128_h128_layer1/2026-02-19_12-10-22" \
      --timelimits "$T" --searchlog --cachescope problem \
      "$DATA" False 128 128 1 $COMMON
  # フォルダ名だけでは計測の実行と区別できないので、末尾に _searchlog を付ける
  OUT=$(sed -n 's|^Run config saved to: \(.*\)/config.json$|\1|p' "$LAST_LOG" | head -1)
  if [ -n "$OUT" ] && [ -d "$OUT" ]; then
    mv "$OUT" "${OUT}_searchlog" && echo "renamed: $OUT -> ${OUT}_searchlog"
  fi
done

# --- 1周目: T30000 ---
for entry in "${REUSE_RUNS[@]}"; do
  read -r DIR BI EMB LAYERS <<< "$entry"
  run "reuse_bi${BI}_i${EMB}_layer${LAYERS}_T30000" --reuse "$DIR" --timelimits 30000 $OPTS \
      "$DATA" "$BI" "$EMB" "$EMB" "$LAYERS" $COMMON
done

# 512 次元の双方向はどちらの回でも学習まで進んでいないので、学習からやり直す
for LAYERS in 1 2; do
  run "train_biTrue_i512_layer${LAYERS}_T30000" --timelimits 30000 $OPTS \
      "$DATA" True 512 512 "$LAYERS" $COMMON
done

# --- 2周目: 時間制限ごとにキャッシュを空にして T30000 ---
# 時間制限ごとに空にしても時間制限どうしは独立なので、T30000 だけで比べられる。
TL_OPTS="--sequential --cachescope timelimit"
for entry in "${REUSE_RUNS[@]}"; do
  read -r DIR BI EMB LAYERS <<< "$entry"
  run "reuse_bi${BI}_i${EMB}_layer${LAYERS}_T30000_cachetimelimit" --reuse "$DIR" --timelimits 30000 $TL_OPTS \
      "$DATA" "$BI" "$EMB" "$EMB" "$LAYERS" $COMMON
done

# 1周目で学習したモデルを使う（学習に失敗していれば飛ばす）
for LAYERS in 1 2; do
  DIR=$(ls -td "$R"/jsem_biTrue_s32_lr5.0e-4_i512_h512_layer${LAYERS}/*/topk_nothing_cache-problem 2>/dev/null | head -1)
  if [ -n "$DIR" ] && [ -f "$DIR/seq-class.model" ]; then
    run "reuse_biTrue_i512_layer${LAYERS}_T30000_cachetimelimit" --reuse "$DIR" --timelimits 30000 $TL_OPTS \
        "$DATA" True 512 512 "$LAYERS" $COMMON
  else
    echo "skipped: no trained model for biTrue i512 layer$LAYERS"
  fi
done

# --- 3周目: 問題ごとにキャッシュを空にして T60000, T90000 ---
for entry in "${REUSE_RUNS[@]}"; do
  read -r DIR BI EMB LAYERS <<< "$entry"
  run "reuse_bi${BI}_i${EMB}_layer${LAYERS}_T60000-90000" --reuse "$DIR" --timelimits 60000,90000 $OPTS \
      "$DATA" "$BI" "$EMB" "$EMB" "$LAYERS" $COMMON
done

# 1周目で学習したモデルを使う（学習に失敗していれば飛ばす）
for LAYERS in 1 2; do
  DIR=$(ls -td "$R"/jsem_biTrue_s32_lr5.0e-4_i512_h512_layer${LAYERS}/*/topk_nothing_cache-problem 2>/dev/null | head -1)
  if [ -n "$DIR" ] && [ -f "$DIR/seq-class.model" ]; then
    run "reuse_biTrue_i512_layer${LAYERS}_T60000-90000" --reuse "$DIR" --timelimits 60000,90000 $OPTS \
        "$DATA" True 512 512 "$LAYERS" $COMMON
  else
    echo "skipped: no trained model for biTrue i512 layer$LAYERS"
  fi
done

echo "All queued runs finished."
