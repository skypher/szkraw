#!/bin/bash
# Poll a pro-cli job; heartbeat line per minute; save result when done.
JOB=$1; OUT=${2:-/home/yang/szkraw/reviews/limits-review-answer.md}; LOG=${3:-/home/yang/szkraw/runs/review/poll.log}
q() { ssh -o ConnectTimeout=20 procli "pro-cli $(printf '%q ' "$@")"; }
start=$(date +%s)
while true; do
  st=$(q job status "$JOB" 2>&1 | python3 -c "import json,sys
try:
  d=json.load(sys.stdin); print(d['data']['job']['status'])
except Exception as e: print('status-error')")
  echo "[$(date '+%H:%M:%S')] job $JOB status=$st elapsed=$(( ($(date +%s)-start)/60 ))min" >> "$LOG"
  case "$st" in
    completed|succeeded|done|finished)
      q job result "$JOB" > /home/yang/szkraw/runs/review/result.json 2>&1
      python3 -c "import json;d=json.load(open('/home/yang/szkraw/runs/review/result.json'));print(d['data']['result'] if isinstance(d['data']['result'],str) else d['data']['result'].get('text',json.dumps(d['data']['result'])))" > "$OUT" 2>>"$LOG"
      echo "[$(date '+%H:%M:%S')] saved $(wc -c < "$OUT") bytes to $OUT" >> "$LOG"; exit 0;;
    failed|error|cancelled|canceled)
      q job status "$JOB" > /home/yang/szkraw/runs/review/final-status.json 2>&1; echo "[$(date '+%H:%M:%S')] job ended: $st" >> "$LOG"; exit 1;;
  esac
  sleep 60
done
