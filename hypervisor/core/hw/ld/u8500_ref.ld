__page_size__ = 0x1000; /*4KB page size*/
__ram_start__ = 0x00000000;
__ram_end__   = 0x01000000;
__hyper_stack_top__ = 0x100000 - 4; /* Hypervisor stack located at end of hypervisor address. Changed __hyperstack_top__ to __hyper_stack_top__ since core/hw/cpu/arm/armv7a/boot.S refers to that symbol. This was needed to make u8500 compilable. */

MEMORY 
{
    RAM : org = 0x00000000, l = 0x01000000
}

ENTRY(_start) 
 
SECTIONS
{
    . = __ram_start__;
    
    /* code: startup first */
    .text : {
        __startup_start__ = .;      
        *(.startup)
        __startup_end__ = .;
        __code_start__ = .;
        *.o (.text)
        *.to(.text)
        __code_end__ = .;
        
    } > RAM
        
    /* DATA */
    .data : {
        __data_start__ = .;        
        *.o (.data)
        *.to(.data)
        __data_end__ = .;
    } > RAM

    /* BSS: Changed to the same layout as for Beaglebone when making u8500 compilable. */
    __hyper_bss_start__ = .;
    .bss  : {
        *.o (.bss)
        *.to(.bss)
    } > RAM
    __hyper_bss_end__ = .;


	/* Added the following to make u8500 compilable. */

	/* HEAP: Added to give same memory layout as for Beaglebone. */
	/* heap: 104k. */
    __hyper_heap_start__ = .;    
    . += 1024 * (64 + 32 + 8);
    __hyper_heap_end__ = .;

	/* STACK: Added to give same memory layout as for Beaglebone. */
    /* stack */
    __hyper_stack_bottom__ = .;
    . += 1024 * 8;
    __hyper_stack_top__ = .;         

	/* GUEST: Added to give same memory layout as for Beaglebone. */
    /* guest */
    __hyper_guest_start__ = .;
    . += 1024 * 32;
    __hyper_guest_end__ = .;     
    
	/* PT MEMORY: Added to give same memory layout as for Beaglebone. */
    /* PT memory */    
    . = ALIGN(__page_size__);
    __hyper_pt_start__ = .;
    . += 1024 * 64;    
    __hyper_pt_end__ = .;

    __hyper_end__ = .;    

}
