# minirubik Stage 4, version 1: a correct RV32I IDA* solver, not tuned for speed.
# Assemble together with the generated tables:
#     cat solver_v1.s tables.s > full.s
# The input state is the 14-character string at "input" below.
#
# Output: the moves on one line, then the length; exit code 0 if the returned
# path, applied with the transition tables, reaches the solved state,
# 1 if it does not, 2 if the input is not a valid state.

.data
# Search stack: one 16-byte frame per depth, frames 0 to 11.
#   +0 sp  (half) permutation rank of the state expanded at this depth
#   +2 so  (half) orientation rank of that state
#   +4 cp  (half) permutation rank after the turns tried so far
#   +6 co  (half) orientation rank after the turns tried so far
#   +8 face (byte)  +9 turn (byte)  +10 last face (byte)
frames: .zero 192
# path[g] = (face << 2) | turn, one byte per depth (12 used, padded to 16)
path:   .zero 16
# 14 characters + NUL, padded to 16 so that the tables stay aligned
input:  .string "21345671111111"
        .zero 1

.text
main:
# ---------------------------------------------------------------------------
# Parse and validate. a0 = p rank, a1 = o rank.
#   t0 = pointer into input, t1 = character, t2 = bit mask of cubies seen,
#   t3 = orientation sum, t4 = loop counter
# ---------------------------------------------------------------------------
    la   t0, input
    li   t2, 0
    li   t4, 7
check_p:                         # characters 0..6 must be '1'..'7', all different
    lbu  t1, 0(t0)
    addi t1, t1, -49             # '1' -> 0
    li   t5, 7
    bgeu t1, t5, invalid         # unsigned compare also rejects chars < '1'
    li   t5, 1
    sll  t5, t5, t1
    and  t6, t2, t5
    bnez t6, invalid             # repeated cubie
    or   t2, t2, t5
    addi t0, t0, 1
    addi t4, t4, -1
    bnez t4, check_p

    li   t3, 0
    li   t4, 7
check_o:                         # characters 7..13 must be '1'..'3'
    lbu  t1, 0(t0)
    addi t1, t1, -49
    li   t5, 3
    bgeu t1, t5, invalid
    add  t3, t3, t1
    addi t0, t0, 1
    addi t4, t4, -1
    bnez t4, check_o
    lbu  t1, 0(t0)
    bnez t1, invalid             # exactly 14 characters
    li   t5, 0x1249              # bits 0, 3, 6, 9, 12: multiples of 3
    srl  t5, t5, t3
    andi t5, t5, 1
    beqz t5, invalid

# Permutation rank (Lehmer code, Horner form): a0 = a0 * (7 - i) + smaller_i.
# Multiplying by k is k repeated additions; this runs once per input.
    la   t0, input
    li   a0, 0
    li   t4, 7                   # t4 = 7 - i = number of characters from i on
rank_p_loop:
    mv   t5, a0                  # a0 = a0 * t4
    li   a0, 0
    mv   t6, t4
mul_loop:
    add  a0, a0, t5
    addi t6, t6, -1
    bnez t6, mul_loop
    lbu  t1, 0(t0)               # value at position i
    li   t3, 0                   # smaller
    addi a2, t0, 1
    add  a3, t0, t4              # one past position 6
count_loop:
    bgeu a2, a3, count_done
    lbu  a4, 0(a2)
    sltu a5, a4, t1
    add  t3, t3, a5
    addi a2, a2, 1
    j    count_loop
count_done:
    add  a0, a0, t3
    addi t0, t0, 1
    addi t4, t4, -1
    bnez t4, rank_p_loop

# Orientation rank: base 3 over the first six orientation digits.
    la   t0, input
    addi t0, t0, 7
    li   a1, 0
    li   t4, 6
rank_o_loop:
    lbu  t1, 0(t0)
    addi t1, t1, -49
    slli t5, a1, 1
    add  a1, a1, t5              # a1 * 3
    add  a1, a1, t1
    addi t0, t0, 1
    addi t4, t4, -1
    bnez t4, rank_o_loop

# ---------------------------------------------------------------------------
# Table bases, kept in saved registers for the whole search.
# ---------------------------------------------------------------------------
    la   s3, tp0
    la   s4, tp1
    la   s5, tp2
    la   s6, to0
    la   s7, to1
    la   s8, to2
    la   s9, pdb_p
    la   s10, pdb_o
    la   s11, path
    mv   a6, a0                  # keep the root ranks for the path check
    mv   a7, a1

# h(root) = max(pdb_p[p], pdb_o[o])
    add  t0, s9, a0
    lbu  t0, 0(t0)
    add  t1, s10, a1
    lbu  t1, 0(t1)
    bgeu t0, t1, 1f
    mv   t0, t1
1:
    li   s2, 0                   # s2 = solution length
    beqz t0, verify              # already solved
    mv   s0, t0                  # s0 = bound

# ---------------------------------------------------------------------------
# Iterative deepening. s0 = bound, s1 = current frame, s2 = g.
# ---------------------------------------------------------------------------
bound_loop:
    la   s1, frames
    li   s2, 0
    sh   a6, 0(s1)               # sp = cp = p
    sh   a6, 4(s1)
    sh   a7, 2(s1)               # so = co = o
    sh   a7, 6(s1)
    sb   zero, 8(s1)             # face = 0
    sb   zero, 9(s1)             # turn = 0
    li   t0, 255
    sb   t0, 10(s1)              # no previous face at the root

search_loop:
    lbu  t0, 9(s1)               # turn
    li   t6, 3
    bne  t0, t6, 2f              # all three turns of this face used?
    lbu  t1, 8(s1)
    addi t1, t1, 1
    sb   t1, 8(s1)
    sb   zero, 9(s1)
    lhu  t2, 0(s1)
    sh   t2, 4(s1)
    lhu  t2, 2(s1)
    sh   t2, 6(s1)
2:
    lbu  t1, 8(s1)               # face
    lbu  t2, 10(s1)              # last face
    bne  t1, t2, 3f              # never turn the same face twice
    addi t1, t1, 1
    sb   t1, 8(s1)
    sb   zero, 9(s1)
    lhu  t2, 0(s1)
    sh   t2, 4(s1)
    lhu  t2, 2(s1)
    sh   t2, 6(s1)
3:
    lbu  t1, 8(s1)
    bne  t1, t6, 4f              # face == 3: no children left
    beqz s2, next_bound          # backtrack from the root: this bound failed
    addi s2, s2, -1
    addi s1, s1, -16
    j    search_loop
4:
    lbu  t0, 9(s1)               # turn, then turn + 1
    addi t2, t0, 1
    sb   t2, 9(s1)
    mv   t3, s3                  # select the face's two tables
    mv   t4, s6
    beqz t1, 5f
    mv   t3, s4
    mv   t4, s7
    li   t5, 1
    beq  t1, t5, 5f
    mv   t3, s5
    mv   t4, s8
5:
    lhu  t2, 4(s1)               # cp = tp[face][cp]
    slli t2, t2, 1
    add  t2, t3, t2
    lhu  t2, 0(t2)
    sh   t2, 4(s1)
    lhu  t5, 6(s1)               # co = to[face][co]
    slli t5, t5, 1
    add  t5, t4, t5
    lhu  t5, 0(t5)
    sh   t5, 6(s1)
    add  a2, s9, t2              # hh = max(pdb_p[cp], pdb_o[co])
    lbu  a2, 0(a2)
    add  a3, s10, t5
    lbu  a3, 0(a3)
    bgeu a2, a3, 6f
    mv   a2, a3
6:
    addi a3, s2, 1               # g + 1 + hh > bound: pruned
    add  a4, a3, a2
    bltu s0, a4, search_loop
    slli a4, t1, 2               # path[g] = (face << 2) | turn
    or   a4, a4, t0
    add  a5, s11, s2
    sb   a4, 0(a5)
    beqz a2, found
    sh   t2, 16(s1)              # push the child: sp = cp, so = co
    sh   t2, 20(s1)
    sh   t5, 18(s1)
    sh   t5, 22(s1)
    sb   zero, 24(s1)            # face = 0
    sb   zero, 25(s1)            # turn = 0
    sb   t1, 26(s1)              # last face = face
    addi s1, s1, 16
    addi s2, s2, 1
    j    search_loop

next_bound:
    addi s0, s0, 1
    li   t0, 11
    bgeu t0, s0, bound_loop
    li   a0, 1                   # no solution within 11: should not happen
    j    exit

found:
    addi s2, s2, 1               # solution length = g + 1

# ---------------------------------------------------------------------------
# In-program check (T5): apply the path to the root ranks with the
# transition tables; the result must be (0, 0). Also print each move.
#   t0 = index, s0/s1 = current p/o ranks (the search no longer needs them)
# ---------------------------------------------------------------------------
verify:
    mv   s0, a6
    mv   s1, a7
    li   a7, 11                  # every print below is "print character"
    li   t0, 0
verify_loop:
    bgeu t0, s2, verify_done
    add  t1, s11, t0
    lbu  t1, 0(t1)
    srli t2, t1, 2               # face
    andi t3, t1, 3               # turn: apply turn + 1 quarter turns
    mv   t4, s3
    mv   t5, s6
    li   a0, 82                  # 'R'
    beqz t2, 7f
    mv   t4, s4
    mv   t5, s7
    li   a0, 66                  # 'B'
    li   t6, 1
    beq  t2, t6, 7f
    mv   t4, s5
    mv   t5, s8
    li   a0, 68                  # 'D'
7:
    ecall                        # face letter
    beqz t3, 9f                  # suffix: none, '2', or '\''
    li   a0, 50                  # '2'
    li   t6, 1
    beq  t3, t6, 8f
    li   a0, 39                  # '\''
8:
    ecall
9:
    addi t6, t3, 1               # quarter turns to apply
turn_loop:
    slli a2, s0, 1
    add  a2, t4, a2
    lhu  s0, 0(a2)
    slli a2, s1, 1
    add  a2, t5, a2
    lhu  s1, 0(a2)
    addi t6, t6, -1
    bnez t6, turn_loop
    li   a0, 32                  # space
    ecall
    addi t0, t0, 1
    j    verify_loop
verify_done:
    li   a0, 10                  # newline, then the length
    ecall
    mv   a0, s2
    li   a7, 1
    ecall
    li   a0, 10
    li   a7, 11
    ecall
    or   t0, s0, s1              # both ranks must be 0
    snez a0, t0                  # 0 = path solves the state, 1 = it does not
    j    exit

invalid:
    li   a0, 2

exit:
    li   a7, 93                  # exit with code a0
    ecall
