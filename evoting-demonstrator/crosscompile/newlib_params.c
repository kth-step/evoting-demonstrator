
/*
/usr/arm-none-eabi/lib/librdimon.a(arm_librdimon_a-syscalls.o): in function `_sbrk':
syscalls.c:(.text._sbrk+0x78): undefined reference to `end'
see libgloss/arm/syscalls.c

extern char   end asm ("end"); // Defined by the linker.
if (xyz)
  heap_end = &end

*/

// refer to link script cake_guest.ld variable where [] accesses the variable
// https://sourceware.org/binutils/docs/ld/Source-Code-Reference.html
// extern char __trusted_heap_end__[];
// const char end = (char)&__trusted_heap_end__[0];

/*
/usr/arm-none-eabi/lib/libc.a(libc_a-fini.o): in function `__libc_fini_array':
.../newlib-4.3.0.20230120/newlib/libc/misc/fini.c:36:(.text.__libc_fini_array+0x30): undefined reference to `_fini'

newlib/libc/misc/fini.c
*/
void _fini (void) { };

