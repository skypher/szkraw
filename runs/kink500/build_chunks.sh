#!/bin/bash
# Build the N = 500 kernel certificate (P3 one-kink example) with progress: lake builds the four chunk modules
# (in parallel); each finished module is reported by lake. Memory is sampled every 5 s (summed RSS of the running
# chunk checks); a heartbeat every 30 s lists the running checks with elapsed time and RSS, and the current and
# peak summed RSS. Finished chunks persist as .olean files, so a rerun resumes; --clean removes them first, so
# that all four chunks are checked in the same run.
# Usage: build_chunks.sh LOG [TARGET] [--clean]
LOG=${1:-/home/yang/szkraw/runs/kink500/build.log}; TARGET=${2:-Szkraw.Kink500}
cd /home/yang/szkraw/lean || exit 1
export PATH=$HOME/.elan/bin:$PATH
if [ "$3" = "--clean" ]; then
  rm -f .lake/build/lib/lean/Szkraw/Kink500Chunk?.* .lake/build/lib/lean/Szkraw/Kink500.*
  echo "[$(date +%H:%M:%S)] removed the chunk build outputs" >> "$LOG"
fi
monitor() {
  peak=0; n=0
  while true; do
    sleep 5; n=$((n + 1))
    sum=$(ps -eo rss,args | awk '/[l]ean .*Kink500Chunk[0-9]/ {s += $1} END {print s + 0}')
    [ "$sum" -gt "$peak" ] && peak=$sum
    echo "$peak" > "$LOG.peak"
    if [ $((n % 6)) -eq 0 ]; then
      running=$(ps -eo etimes,rss,args | awk '/[l]ean .*Kink500Chunk[0-9]/ {match($0, /Kink500Chunk[0-9]/); printf "%s %ss %.1fGB; ", substr($0, RSTART, RLENGTH), $1, $2/1e6}')
      done_n=$(ls .lake/build/lib/lean/Szkraw/Kink500Chunk?.olean 2>/dev/null | wc -l)
      echo "[$(date +%H:%M:%S)] heartbeat: $done_n/4 chunks done; running: ${running:-none} summed RSS $(awk "BEGIN {printf \"%.1f\", $sum/1e6}") GB, peak $(awk "BEGIN {printf \"%.1f\", $peak/1e6}") GB"
    fi
  done
}
monitor >> "$LOG" &
HB=$!
echo "[$(date +%H:%M:%S)] start lake build $TARGET" >> "$LOG"
stdbuf -oL lake build "$TARGET" 2>&1 | while IFS= read -r line; do echo "[$(date +%H:%M:%S)] $line"; done >> "$LOG"
rc=${PIPESTATUS[0]}
sleep 6
kill "$HB"
PEAK=$(cat "$LOG.peak" 2>/dev/null || echo 0)
echo "[$(date +%H:%M:%S)] lake build exit $rc; peak summed RSS of the chunk checks $(awk "BEGIN {printf \"%.1f\", $PEAK/1e6}") GB (5 s sampling)" >> "$LOG"
