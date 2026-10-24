/* Flat memory: code and data from 64 KiB, heap after .bss, stack at 64 MiB.
   The emulator (../emu) maps 128 MiB and puts the witness at 0x06000000. */
ENTRY(_start)

MEMORY
{
  RAM : ORIGIN = 0x00010000, LENGTH = 0x03FF0000
}

SECTIONS
{
  .text : { KEEP(*(.text.init)) *(.text .text.*) } > RAM
  .rodata : ALIGN(8) { *(.rodata .rodata.*) *(.srodata .srodata.*) } > RAM
  .data : ALIGN(8) { *(.data .data.*) *(.sdata .sdata.*) } > RAM
  .bss : ALIGN(8) { *(.bss .bss.*) *(.sbss .sbss.*) *(COMMON) } > RAM
  . = ALIGN(16);
  __heap_start = .;
  __stack_top = 0x04000000;
}
