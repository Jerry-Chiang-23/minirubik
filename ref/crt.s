    .globl _start
    .text
_start:
    li   sp, 0x3ffffff0
    call main
    li   a7, 93
    ecall
