ENTRY(_start)
SECTIONS {
  . = 0x0;
  .text : { *(.text .text.*) }
  . = 0x10000000;
  .data : { *(.data .data.* .rodata .rodata.* .sdata .sdata.* .srodata .srodata.* ) }
  .bss : { *(.bss .bss.* .sbss .sbss.* COMMON) }
}
