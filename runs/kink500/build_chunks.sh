#!/bin/bash
# Build the N = 500 kernel certificate (P3 one-kink example) with progress: lake builds the four chunk modules
# (in parallel); each finished module is reported by lake, and a heartbeat every 30 s lists the running chunk
# checks with elapsed time and RSS. Finished chunks persist as .olean files, so a rerun resumes.
# Usage: build_chunks.sh LOG [TARGET]
LOG=${1:-/home/yang/szkraw/runs/kink500/build.log}; TARGET=${2:-Szkraw.Kink500}
cd /home/yang/szkraw/lean || exit 1
export PATH=$HOME/.elan/bin:$PATH
heartbeat() {
  while true; do
    sleep 30
    running=$(ps -eo etimes,rss,args | awk '/[l]ean .*Kink500Chunk[0-9]/ {match($0, /Kink500Chunk[0-9]/); printf "%s %ss %.1fGB; ", substr($0, RSTART, RLENGTH), $1, $2/1e6}')
    done_n=$(ls .lake/build/lib/lean/Szkraw/Kink500Chunk?.olean 2>/dev/null | wc -l)
    echo "[$(date +%H:%M:%S)] heartbeat: $done_n/4 chunks done; running: ${running:-none}"
  done
}
heartbeat >> "$LOG" &
HB=$!
echo "[$(date +%H:%M:%S)] start lake build $TARGET" >> "$LOG"
stdbuf -oL lake build "$TARGET" 2>&1 | while IFS= read -r line; do echo "[$(date +%H:%M:%S)] $line"; done >> "$LOG"
rc=${PIPESTATUS[0]}
kill "$HB"
echo "[$(date +%H:%M:%S)] lake build exit $rc" >> "$LOG"
