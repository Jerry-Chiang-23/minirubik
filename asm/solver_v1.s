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
    la   s1, frames              # keep the root ranks in frames[0] for the path check
    sh   a0, 0(s1)
    sh   a1, 2(s1)

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
    lhu  t0, 0(s1)               # t0 = sp, t1 = so: root ranks
    lhu  t1, 2(s1)
    li   t6, 255                 # t6 = last face: none at the root
    li   a4, 3                   # a4 = 3 for the whole search (loop limits)
node_enter:                      # a node: t0/t1 = its p/o ranks, s2 = g
    sub  a5, s0, s2
    addi a5, a5, -1              # a5 = bound - (g + 1): the largest h a child may have
    li   t4, 0                   # t4 = face
face_loop:
    beq  t4, t6, next_face       # never turn the same face twice
    jal  ra, sel_tables          # a6 = tp[face], a7 = to[face]
    mv   t2, t0                  # t2 = cp, t3 = co: start from the node's own state
    mv   t3, t1
turn0:                         # turn 1 of this face (unrolled)
    slli a0, t2, 1               # cp = tp[face][cp]
    add  a0, a0, a6
    lhu  t2, 0(a0)
    slli a1, t3, 1               # co = to[face][co]
    add  a1, a1, a7
    lhu  t3, 0(a1)
    add  a2, s9, t2              # h_p = pdb_p[cp]
    lbu  a2, 0(a2)
    bltu a5, a2, turn1
    add  a3, s10, t3             # h = max(h_p, pdb_o[co])
    lbu  a3, 0(a3)
    bgeu a2, a3, 10f
    mv   a2, a3
10:
    bltu a5, a2, turn1           # h > bound - (g + 1): pruned
    li   t5, 0
    j    survive
turn1:                         # turn 2 of this face (unrolled)
    slli a0, t2, 1               # cp = tp[face][cp]
    add  a0, a0, a6
    lhu  t2, 0(a0)
    slli a1, t3, 1               # co = to[face][co]
    add  a1, a1, a7
    lhu  t3, 0(a1)
    add  a2, s9, t2              # h_p = pdb_p[cp]
    lbu  a2, 0(a2)
    bltu a5, a2, turn2
    add  a3, s10, t3             # h = max(h_p, pdb_o[co])
    lbu  a3, 0(a3)
    bgeu a2, a3, 11f
    mv   a2, a3
11:
    bltu a5, a2, turn2           # h > bound - (g + 1): pruned
    li   t5, 1
    j    survive
turn2:                         # turn 3 of this face (unrolled)
    slli a0, t2, 1               # cp = tp[face][cp]
    add  a0, a0, a6
    lhu  t2, 0(a0)
    slli a1, t3, 1               # co = to[face][co]
    add  a1, a1, a7
    lhu  t3, 0(a1)
    add  a2, s9, t2              # h_p = pdb_p[cp]
    lbu  a2, 0(a2)
    bltu a5, a2, next_face
    add  a3, s10, t3             # h = max(h_p, pdb_o[co])
    lbu  a3, 0(a3)
    bgeu a2, a3, 12f
    mv   a2, a3
12:
    bltu a5, a2, next_face           # h > bound - (g + 1): pruned
    li   t5, 2
survive:                         # the child passed the bound; t5 = its turn
    slli a0, t4, 2               # path[g] = (face << 2) | turn
    or   a0, a0, t5
    add  a1, s11, s2
    sb   a0, 0(a1)
    beqz a2, found
    sh   t0, 0(s1)               # push: save this node's registers, descend
    sh   t1, 2(s1)
    sh   t2, 4(s1)
    sh   t3, 6(s1)
    sb   t4, 8(s1)
    sb   t5, 9(s1)
    sb   t6, 10(s1)
    mv   t0, t2                  # the child's p/o are cp/co
    mv   t1, t3
    mv   t6, t4                  # the child's last face is this face
    addi s1, s1, 16
    addi s2, s2, 1
    j    node_enter
next_face:
    addi t4, t4, 1
    blt  t4, a4, face_loop
    beqz s2, next_bound          # backtrack from the root: this bound failed
    addi s2, s2, -1              # pop: restore the parent's registers
    addi s1, s1, -16
    lhu  t0, 0(s1)
    lhu  t1, 2(s1)
    lhu  t2, 4(s1)
    lhu  t3, 6(s1)
    lbu  t4, 8(s1)
    lbu  t5, 9(s1)
    lbu  t6, 10(s1)
    sub  a5, s0, s2
    addi a5, a5, -1
    jal  ra, sel_tables
    beqz t5, turn1               # carry on with the parent's next turn
    li   a0, 1
    beq  t5, a0, turn2
    j    next_face

sel_tables:                      # a6/a7 = the transition tables of face t4
    mv   a6, s3
    mv   a7, s6
    beqz t4, 2f
    mv   a6, s4
    mv   a7, s7
    li   a0, 1
    beq  t4, a0, 2f
    mv   a6, s5
    mv   a7, s8
2:
    ret

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
    la   t1, frames              # the root ranks saved in frames[0]
    lhu  s0, 0(t1)
    lhu  s1, 2(t1)
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
    mv   s4, a0                  # RENDER
    la   a0, input               # RENDER
    jal  ra, led_init            # RENDER
    li   s3, 0                   # RENDER
led_loop:                        # RENDER
    bgeu s3, s2, led_done        # RENDER
    add  t1, s11, s3             # RENDER
    lbu  a0, 0(t1)               # RENDER
    jal  ra, led_move            # RENDER
    addi s3, s3, 1               # RENDER
    j    led_loop                # RENDER
led_done:                        # RENDER
    mv   a0, s4                  # RENDER
    j    exit

invalid:
    li   a0, 2

exit:
    li   a7, 93                  # exit with code a0
    ecall
