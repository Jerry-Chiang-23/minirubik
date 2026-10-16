#!/bin/bash
# repro.sh -- re-run every measurement quoted in the HackMD note and print a log.
# Run from the repository root (WSL):   ./repro.sh 2>&1 | tee repro_log.txt
# Needs: git, riscv64-unknown-elf-{as,ld,size,gcc}, and Ripes (same build as the note).
set -u
RIPES=${RIPES:-/mnt/d/Ripes-v2.2.6/Ripes.exe}
TABLES=${TABLES:-tables.s}
COMMITS=${COMMITS:-"0450832 527ded6 e0e7150 8254e73 77adc58"}   # A B C D E
INPUTS=${INPUTS:-"25416373331111 21345671111111 54721631111111"}
SMALL=${SMALL:-25416373331111}                                   # input used for RV32_5S cycles
WORK=${WORK:-$(dirname "$RIPES")/repro_tmp}
mkdir -p "$WORK"
winpath() { if command -v wslpath >/dev/null 2>&1 && [[ "$RIPES" == *.exe ]]; then wslpath -w "$1"; else echo "$1"; fi; }
# run_ripes <file> <asm|elf> <proc>  -> prints "retired cycles exit"
run_ripes() {
  local out r c e try
  for try in 1 2 3; do
    if [ -n "${RIPES_WRAP:-}" ]; then out=$("$RIPES_WRAP" "$1" "$2" "$3" 2>&1)
    elif [[ "$RIPES" == *.exe ]]; then
      # WSL cannot exec this GUI-type .exe directly ("Exec format error"); go through cmd.exe from a drive path
      out=$(cd "$(dirname "$RIPES")" && cmd.exe /c "$(basename "$RIPES") --mode cli --src $(wslpath -w "$1") -t $2 --proc $3 --iret --cycles --timeout 900000" 2>&1)
    else out=$("$RIPES" --mode cli --src "$1" -t "$2" --proc "$3" --iret --cycles --timeout 900000 2>&1); fi
    out=$(printf '%s\n' "$out" | tr -d '\r' | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//')
    r=$(printf '%s\n' "$out" | awk '/instructions retired/ && !/per/ {getline; print; exit}')
    [ -n "$r" ] && break
    sleep 2        # Ripes sometimes exits without output when started back-to-back: retry
  done
  c=$(printf '%s\n' "$out" | awk '/^=+ *cycles$/ {getline; print; exit}')
  e=$(printf '%s\n' "$out" | sed -n 's/.*exited with code: *//p' | head -1)
  [ -n "${REPRO_DEBUG:-}" ] && { echo "--- raw output of $1 ($3) ---" >&2; printf '%s\n' "$out" | head -20 >&2; }
  echo "${r:-?} ${c:-?} ${e:-?}"
}
mkasm() { # <commit> <input> <outfile>
  { git show "$1:asm/solver_v1.s" | sed '/# RENDER$/d' | sed -E "s/^(input:[[:space:]]+\.string )\"[0-9]*\"/\1\"$2\"/"; echo; cat "$TABLES"; } > "$3"
}
sizes() { # <asm file> -> ".text .data" via GNU as/ld
  riscv64-unknown-elf-as -march=rv32i -mabi=ilp32 "$1" -o "$1.o" && \
  riscv64-unknown-elf-ld -m elf32lriscv -Ttext=0 -Tdata=0x10000000 "$1.o" -o "$1.elf" 2>/dev/null
  riscv64-unknown-elf-size -A "$1.elf" | awk '/^\.text/{t=$2} /^\.data/{d=$2} END{print t, d}'
}

echo "== environment =="
date; uname -a
echo "git HEAD: $(git rev-parse --short HEAD)   tables: $(sha256sum "$TABLES" | cut -c1-16)"
riscv64-unknown-elf-gcc --version | head -1
echo "Ripes: $RIPES"
echo
echo "== A-E: retired instructions (RV32_ISS), exit code =="
printf "%-9s %-16s %14s %5s\n" commit input retired exit
for c in $COMMITS; do
  for v in $INPUTS; do
    f="$WORK/r_${c}_$v.s"; mkasm "$c" "$v" "$f"
    read -r r cy e < <(run_ripes "$f" asm RV32_ISS)
    printf "%-9s %-16s %14s %5s\n" "$c" "$v" "$r" "$e"
  done
done
echo
echo "== A-E: linked .text / .data bytes (GNU as/ld, renderer removed) =="
printf "%-9s %8s %8s %12s\n" commit text data instr_count
for c in $COMMITS; do
  f="$WORK/s_$c.s"; mkasm "$c" 21345671111111 "$f"
  read -r t d < <(sizes "$f")
  n=$(riscv64-unknown-elf-objdump -d "$f.elf" | grep -c '^ *[0-9a-f]*:')
  printf "%-9s %8s %8s %12s\n" "$c" "$t" "$d" "$n"
done
echo
echo "== A-E: RV32_5S cycles and retired on $SMALL =="
printf "%-9s %12s %12s\n" commit retired cycles
for c in $COMMITS; do
  f="$WORK/r_${c}_$SMALL.s"; [ -f "$f" ] || mkasm "$c" "$SMALL" "$f"
  read -r r cy e < <(run_ripes "$f" asm RV32_5S)
  printf "%-9s %12s %12s\n" "$c" "$r" "$cy"
done
echo
if [ -f ref/build.sh ]; then
  echo "== gcc -O2 reference (ref/build.sh) =="
  printf "%-16s %12s %12s %8s\n" input retired_ISS cycles_5S exit
  for v in $INPUTS; do
    bash ref/build.sh "$v" "$WORK/gcc_$v.elf" -O2 > "$WORK/gcc_$v.log" 2>&1
    read -r r cy e < <(run_ripes "$WORK/gcc_$v.elf" elf RV32_ISS)
    if [ "$v" = "$SMALL" ]; then read -r r2 cy5 e2 < <(run_ripes "$WORK/gcc_$v.elf" elf RV32_5S); else cy5=-; fi
    printf "%-16s %12s %12s %8s\n" "$v" "$r" "$cy5" "$e"
  done
  grep ".text bytes" "$WORK/gcc_$SMALL.log"
fi
echo
echo "== done =="
