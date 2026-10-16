#!/bin/bash
# scan11.sh -- run the final version (commit E) on all 2,644 distance-11 states under Ripes RV32_ISS
# and record retired instructions. Resumable: re-run the same command and it skips finished lines.
# Run from the repository root (WSL), with dist11.txt next to it:
#   ./scan11.sh 2>&1 | tee -a scan11_log.txt
set -u
RIPES=${RIPES:-/mnt/d/Ripes-v2.2.6/Ripes.exe}
COMMIT=${COMMIT:-77adc58}            # E
TABLES=${TABLES:-tables.s}
LIST=${LIST:-dist11.txt}
OUT=${OUT:-scan11.csv}
WORK=${WORK:-$(dirname "$RIPES")/scan11_tmp}
mkdir -p "$WORK"; touch "$OUT"
run_ripes() {   # <asm file> -> "retired exit"
  local out r e try
  for try in 1 2 3; do
    out=$(cd "$(dirname "$RIPES")" && cmd.exe /c "$(basename "$RIPES") --mode cli --src $(wslpath -w "$1") -t asm --proc RV32_ISS --iret --timeout 900000" 2>&1 </dev/null)
    out=$(printf '%s\n' "$out" | tr -d '\r' | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//')
    r=$(printf '%s\n' "$out" | awk '/instructions retired/ && !/per/ {getline; print; exit}')
    [ -n "$r" ] && break
    sleep 2
  done
  e=$(printf '%s\n' "$out" | sed -n 's/.*exited with code: *//p' | head -1)
  echo "${r:-?} ${e:-?}"
}
git show "$COMMIT:asm/solver_v1.s" | sed '/# RENDER$/d' > "$WORK/base.s"
total=$(wc -l < "$LIST"); n=0
while read -r v; do
  n=$((n+1))
  grep -q "^$v," "$OUT" && continue
  f="$WORK/s.s"
  { sed -E "s/^(input:[[:space:]]+\.string )\"[0-9]*\"/\1\"$v\"/" "$WORK/base.s"; echo; cat "$TABLES"; } > "$f"
  read -r r e < <(run_ripes "$f")
  echo "$v,$r,$e" >> "$OUT"
  echo "[$n/$total] $v retired=$r exit=$e"
done < "$LIST"
echo
echo "== summary =="
awk -F, '$2 ~ /^[0-9]+$/ {c++; if ($2>m){m=$2; s=$1}} $2 !~ /^[0-9]+$/ {bad++} END{printf "done=%d  failed(?)=%d  max retired=%d at %s  (%.1f%% of 5e7)\n", c, bad+0, m, s, m/5e7*100}' "$OUT"
echo "exit codes:"; cut -d, -f3 "$OUT" | sort | uniq -c
