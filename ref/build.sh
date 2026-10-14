#!/bin/bash
# Reference build: compile the target-side C with riscv64-unknown-elf-gcc -O2
# -march=rv32i -mabi=ilp32 and link it for Ripes (text at 0x0, data at 0x10000000).
# usage: ref/build.sh [14-digit input] [out.elf] [opt level, default -O2]
set -e
IN=${1:-21345671111111}; OUT=${2:-ref.elf}; OPT=${3:--O2}
HERE=$(cd "$(dirname "$0")" && pwd); TMP=$(mktemp -d)
CF="-march=rv32i -mabi=ilp32"
# tables.s is Ripes-flavoured; give the tables global names and word alignment for GNU as
sed -E 's/^(tp0|tp1|tp2|to0|to1|to2|pdb_p|pdb_o):/    .balign 4\n    .globl \1\n\1:/' "$HERE/../tables.s" > "$TMP/tables_gnu.s"
sed "s/char input\[15\] = \"[0-9]*\"/char input[15] = \"$IN\"/" "$HERE/target.c" > "$TMP/target.c"
riscv64-unknown-elf-gcc $CF $OPT -ffreestanding -fno-builtin -fno-pic -fno-asynchronous-unwind-tables -c "$TMP/target.c" -o "$TMP/target.o"
riscv64-unknown-elf-as $CF "$HERE/crt.s" -o "$TMP/crt.o"
riscv64-unknown-elf-as $CF "$TMP/tables_gnu.s" -o "$TMP/tables.o"
riscv64-unknown-elf-ld -m elf32lriscv -T "$HERE/link.ld" "$TMP/crt.o" "$TMP/target.o" "$TMP/tables.o" -o "$OUT"
echo "undefined library references (must be none):"; riscv64-unknown-elf-nm -u "$TMP/target.o" | grep -v -E " (tp[012]|to[012]|pdb_[po])$" || echo "  none"
riscv64-unknown-elf-size -A "$OUT" | awk '/^\.text/{print ".text bytes (incl. 24-byte crt): " $2}'
rm -rf "$TMP"
