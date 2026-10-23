#!/bin/bash
# Run the committed certificate scripts unmodified from a fresh clone. Usage: run_certs.sh CLONE OUTDIR "path/script.py args" ...
# Each item writes OUTDIR/<n>.out (stdout+stderr) and OUTDIR/<n>.rc; items with an .rc file are skipped on rerun.
CLONE=$1; OUT=$2; shift 2; mkdir -p "$OUT"; n=0; total=$#; rm -f "$OUT/stop"
( while [ ! -f "$OUT/stop" ]; do sleep 30; [ -f "$OUT/stop" ] || echo "[$(date +%H:%M:%S)] heartbeat: $(ls "$OUT"/*.rc 2>/dev/null | wc -l)/$total done, running: $(cat "$OUT/current" 2>/dev/null)"; done ) &
for item in "$@"; do
  n=$((n+1)); script=${item%% *}; args=${item#"$script"}; tag=$(printf '%02d' $n)
  if [ -f "$OUT/$tag.rc" ]; then echo "[$(date +%H:%M:%S)] skip $tag $item (rc $(cat $OUT/$tag.rc))"; continue; fi
  echo "$tag $item" > "$OUT/current"; t0=$(date +%s)
  echo "[$(date +%H:%M:%S)] start $tag/$total: $item  sha256 $(sha256sum "$CLONE/$script" | cut -c1-16)"
  (cd "$CLONE/$(dirname "$script")" && stdbuf -oL python3 "$(basename "$script")" $args) > "$OUT/$tag.out" 2>&1
  rc=$?; echo $rc > "$OUT/$tag.rc"; sync
  echo "[$(date +%H:%M:%S)] end $tag: rc=$rc, $(( $(date +%s) - t0 ))s, last line: $(tail -1 "$OUT/$tag.out" | cut -c1-150)"
done
touch "$OUT/stop"; rm -f "$OUT/current"; echo "[$(date +%H:%M:%S)] all done"
