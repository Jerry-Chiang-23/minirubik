# render.s -- LED-matrix renderer (RV32I, no M extension, no stack, no heap)
# Interface (all clobber only a0-a7, t0-t6; s-registers and ra are preserved):
#   led_init : a0 = address of the 14-digit input string; loads state, draws it
#   led_move : a0 = (face<<2)|turn  (face 0/1/2 = R/B/D, turn 0/1/2 = x1/x2/x3); applies it, redraws
#   led_draw : internal leaf, called with  jal t6, led_draw
# Pixel address = LED_MATRIX_0_BASE + (y*35 + x)*4  (row-major), y*35 = (y<<5)+(y<<1)+y
.text
led_init:
    la   t1, rpc
    la   t2, rpo
    sb   x0, 0(t1)              # position 0 (FUL anchor): cubie 0, twist 0
    sb   x0, 0(t2)
    li   t5, 0
init_l:
    add  a1, a0, t5
    lbu  a2, 0(a1)              # P digit '1'..'7'
    addi a2, a2, -48            # cubie id = digit
    add  a3, t1, t5
    sb   a2, 1(a3)
    lbu  a2, 7(a1)              # O digit '1'..'3'
    addi a2, a2, -49            # twist = digit-1
    add  a3, t2, t5
    sb   a2, 1(a3)
    addi t5, t5, 1
    li   a1, 7
    blt  t5, a1, init_l
    jal  t6, led_draw
    ret

led_move:
    srli a1, a0, 2              # face
    andi a2, a0, 3
    addi a2, a2, 1              # number of quarter turns = turn+1
    slli a3, a1, 3              # face*8
    la   a4, rsrc
    add  a4, a4, a3
    la   a5, rtw
    add  a5, a5, a3
    la   t1, rpc
    la   t2, rtc
    la   t3, rpo
    la   t4, rto
mv_q:
    li   t5, 0
mv_copy:                        # snapshot the current state
    add  a6, t1, t5
    lbu  a7, 0(a6)
    add  a6, t2, t5
    sb   a7, 0(a6)
    add  a6, t3, t5
    lbu  a7, 0(a6)
    add  a6, t4, t5
    sb   a7, 0(a6)
    addi t5, t5, 1
    li   a6, 8
    blt  t5, a6, mv_copy
    li   t5, 1
mv_apply:                       # p'[q]=p[src[q]], o'[q]=(o[src[q]]+tw[q]) mod 3
    add  a6, a4, t5
    lbu  a6, 0(a6)
    add  a7, t2, a6
    lbu  a7, 0(a7)
    add  t6, t1, t5
    sb   a7, 0(t6)
    add  a7, t4, a6
    lbu  a7, 0(a7)
    add  t6, a5, t5
    lbu  t6, 0(t6)
    add  a7, a7, t6
    li   t6, 3
    blt  a7, t6, mv_nomod
    addi a7, a7, -3
mv_nomod:
    add  t6, t3, t5
    sb   a7, 0(t6)
    addi t5, t5, 1
    li   a6, 8
    blt  t5, a6, mv_apply
    addi a2, a2, -1
    bnez a2, mv_q
    jal  t6, led_draw
    ret

led_draw:
    la   t0, LED_MATRIX_0_BASE
    li   a5, 0                  # position p
draw_pos:
    la   a1, rpc
    add  a1, a1, a5
    lbu  t1, 0(a1)              # cubie c at position p
    la   a1, rpo
    add  a1, a1, a5
    lbu  t2, 0(a1)              # its twist o
    slli t3, t1, 3
    add  t3, t3, t1             # c*9
    la   a1, rcol
    add  t3, t3, a1             # &rcol[c][0]
    slli t4, a5, 2
    slli a1, a5, 1
    add  t4, t4, a1             # p*6
    la   a1, rfac
    add  t4, t4, a1             # &rfac[p][0]
    li   a6, 0                  # step s = 0..2 around the corner
draw_st:
    sub  t5, a6, t2             # j = s - o  (mod 3)
    bgez t5, st_ok
    addi t5, t5, 3
st_ok:
    slli a7, t5, 1
    add  t5, a7, t5             # j*3
    add  t5, t5, t3
    lbu  a7, 0(t5)              # R
    lbu  a1, 1(t5)              # G
    lbu  t5, 2(t5)              # B
    slli a7, a7, 8
    or   a7, a7, a1
    slli a7, a7, 8
    or   a7, a7, t5             # 0x00RRGGBB
    lbu  t5, 0(t4)             # x0
    lbu  a0, 1(t4)             # y0
    addi a2, a0, 3
rect_y:
    slli a3, a0, 5
    slli a1, a0, 1
    add  a3, a3, a1
    add  a3, a3, a0             # y*35
    addi a4, t5, 4
    mv   t1, t5
rect_x:
    add  a1, a3, t1
    slli a1, a1, 2
    add  a1, a1, t0
    sw   a7, 0(a1)
    addi t1, t1, 1
    blt  t1, a4, rect_x
    addi a0, a0, 1
    blt  a0, a2, rect_y
    addi t4, t4, 2
    addi a6, a6, 1
    li   a1, 3
    blt  a6, a1, draw_st
    addi a5, a5, 1
    li   a1, 8
    blt  a5, a1, draw_pos
    jr   t6

.data
rpc:  .zero 8
rpo:  .zero 8
rtc:  .zero 8
rto:  .zero 8
rsrc: .byte 0,2,5,3,1,4,6,7, 0,1,2,3,5,6,7,4, 0,1,3,6,4,2,5,7
rtw:  .byte 0,1,2,0,2,1,0,0, 0,0,0,0,1,2,1,2, 0,0,0,0,0,0,0,0
rfac: .byte 9,3,4,7,9,7,13,3,13,7,18,7,13,14,18,10,13,10,9,14,9,10,4,10,13,0,22,7,27,7,13,17,27,10,22,10,9,17,0,10,31,10,9,0,31,7,0,7
.align 2
rcol:
    .byte 0xFF,0xFF,0xFF, 0xFF,0x80,0x00, 0x00,0xFF,0x00
    .byte 0xFF,0xFF,0xFF, 0x00,0xFF,0x00, 0xFF,0x00,0x00
    .byte 0xFF,0xFF,0x00, 0xFF,0x00,0x00, 0x00,0xFF,0x00
    .byte 0xFF,0xFF,0x00, 0x00,0xFF,0x00, 0xFF,0x80,0x00
    .byte 0xFF,0xFF,0xFF, 0xFF,0x00,0x00, 0x00,0x00,0xFF
    .byte 0xFF,0xFF,0x00, 0x00,0x00,0xFF, 0xFF,0x00,0x00
    .byte 0xFF,0xFF,0x00, 0xFF,0x80,0x00, 0x00,0x00,0xFF
    .byte 0xFF,0xFF,0xFF, 0x00,0x00,0xFF, 0xFF,0x80,0x00
