
#include <hw.h>
#include <soc_defs.h>

struct intc_section {
	uint32_t intc_itr;
	uint32_t intc_mir;
	uint32_t intc_mir_clear;
	uint32_t intc_mir_set;
	uint32_t intc_isr_set;
	uint32_t intc_isr_clear;
	uint32_t intc_pending_irq;
	uint32_t intc_pending_fiq;
};

typedef struct {
	uint32_t intc_revision;
	uint32_t unused0[3];
	uint32_t intc_sysconfig;
	uint32_t intc_sysstatus;
	uint32_t unused1[10];
	uint32_t intc_sir_irq;
	uint32_t intc_sir_fiq;
	uint32_t intc_control;
	uint32_t intc_protection;
	uint32_t intc_idle;
	uint32_t unused2[3];
	uint32_t intc_irq_priority;
	uint32_t intc_fiq_priority;
	uint32_t intc_threshold;
	uint32_t unused3[5];
	struct intc_section sections[4];
	uint32_t intc_ilr[128];
} volatile intc_registers;

/* ----------------------------------------------------- */

extern uint32_t *_interrupt_vector_table;
cpu_callback irq_function_table[128] __attribute__ ((aligned(32)));

/*Specifies allowed interrupts on bit level*/
uint32_t interrupt_ctrl[3];

/*Pending interrupts*/
uint32_t pending_interrupt[3];

static volatile intc_registers *intc = 0;

/* static */ return_value default_handler(uint32_t r0, uint32_t r1,
					  uint32_t r2)
{
	printf("HYPERVISOR default_handler (Default Interrupt Handler) %d: 0x%x: 0x%x\n", r0, r1, r2);
	return RV_OK;
}

/*These functions have not been tested yet*/
//UNUSED
void mask_interrupt(uint32_t irq, uint32_t pending)
{
	uint32_t hwirq = irq;
	int offset = irq >> 5;

	irq &= 31;		/*Position of interrupt */

	if (interrupt_ctrl[offset]) {	/*INT CTRL BITMASK IRQ guests are allowed to use */
		//      if(hwirq!=0x44) /*Do not mask timer interrupt*/
		intc->sections[offset].intc_mir_set = (1 << irq);
		if (pending)
			pending_interrupt[offset] |= (1 << irq);
	} else
		hyper_panic("Guest not allowed to use this IRQ", irq);
}

//UNUSED
void unmask_interrupt(uint32_t irq, uint32_t pending)
{
	int offset = irq >> 5;

	irq &= 31;		/*Position of interrupt */

	if (interrupt_ctrl[offset]) {	/*INT CTRL BITMASK IRQ guests are allowed to use */
		intc->sections[offset].intc_mir_clear = (1 << irq);
	} else
		hyper_panic("Guest not allowed to use this IRQ", 0);
}

/*Returns the first true bit*/
uint32_t check_pending_interrupts()
{
	int pending, i = 0;
	for (i = 2; i >= 0; i--) {	/*Prioritize timer interrupt by decrementing loop (IRQ 95) */
		if (pending_interrupt[i]) {
			pending = __builtin_clz(pending_interrupt[i]);	/*Built in GCC function to count leading zeros */

			/*Clear the pending IRQ */
			pending_interrupt[i] &= ~(1 << (31 - pending));

			pending = (31 - pending) + (31 * i) + (i * 1);	/*Get the actual IRQ number */
			return pending;
		}
	}
	return (uint32_t) - 1;	/*No pending interrupts */
}

/* 
 */
int cpu_irq_get_count()
{
	return INTC_SOURCE_COUNT;
}

void cpu_irq_set_enable(int n, BOOL enable)
{
	uint32_t section, pos;

	/* invalid irq number ?? */
	if (n < 0 || n >= INTC_SOURCE_COUNT)
		return;

	section = (n >> 5);
	pos = n & 0x1f;

	/* set or clear interrupt mask for this irq */
	if (enable) {
		intc->sections[section].intc_mir &= ~(1 << pos);
		intc->sections[section].intc_mir_clear = 1 << pos;

		interrupt_ctrl[section] |= (1 << pos);	//UNUSED
	} else {
		intc->sections[section].intc_mir |= (1 << pos);
		intc->sections[section].intc_mir_set = 1 << pos;

		//UNUSED
		interrupt_ctrl[section] &= ~(1 << pos);	/*INT CTRL BITMASK IRQ guests are allowed to use */
	}
}

void cpu_irq_set_handler(int n, cpu_callback handler)
{

	/* invalid irq number ?? */
	if (n < 0 || n >= INTC_SOURCE_COUNT)
		return;

	if (!handler)
		handler = default_handler;

	//set handler
	irq_function_table[n] = handler;
}

void irq_handler();

void soc_interrupt_init()
{
	int i;
	intc = (intc_registers *) IO_VA_OMAP2_L4_ADDRESS(INTC_BASE);
	/* reset the controller */
	intc->intc_sysconfig = INTC_SYSCONFIG_RESET;
	while (!(intc->intc_sysstatus & INTC_SYSSTATUS_RESET_DONE)) ;
	/* turn of all interrupts for now */
	for (i = 0; i < INTC_SOURCE_COUNT; i++) {
		cpu_irq_set_enable(i, FALSE);
		cpu_irq_set_handler(i, default_handler);
	}

	//Enable interrupts for USB for Linux.
	cpu_irq_set_enable(17, TRUE);
	cpu_irq_set_handler(17, (cpu_callback) irq_handler);
//	cpu_irq_set_enable(18, TRUE);							//Unnecessary.
	cpu_irq_set_handler(18, (cpu_callback) irq_handler);	//Unnecessary.
//	cpu_irq_set_enable(19, TRUE);
	cpu_irq_set_handler(19, (cpu_callback) irq_handler);
//	cpu_irq_set_enable(34, TRUE);							//Unnecessary.
	cpu_irq_set_handler(34, (cpu_callback) irq_handler);	//Unnecessary.
//	cpu_irq_set_enable(78, TRUE);							//Unnecessary.
	cpu_irq_set_handler(78, (cpu_callback) irq_handler);	//Unnecessary.

	//Enable Interrupts for CPSW for Linux.
#if defined(LINUX) && defined(CPSW)
	//The network driver uses interrupt lines 40, 41, 42, and 43.
	//Enables interrupts from the Ethernet subsystem and they should be
	//redirected directly to the Linux kernel and therefore they are given the
	//hypervisor interrupt handler irq_handler.
	cpu_irq_set_enable(40, TRUE);
	cpu_irq_set_handler(40, (cpu_callback) irq_handler);
	cpu_irq_set_enable(41, TRUE);
	cpu_irq_set_handler(41, (cpu_callback) irq_handler);
	cpu_irq_set_enable(42, TRUE);
	cpu_irq_set_handler(42, (cpu_callback) irq_handler);
	cpu_irq_set_enable(43, TRUE);
	cpu_irq_set_handler(43, (cpu_callback) irq_handler);
#endif

	//Enable interrupts for DMTIMER2 for Linux.
	cpu_irq_set_enable(68, TRUE);
	cpu_irq_set_handler(68, (cpu_callback) irq_handler);

	//Enable interrupts for I2C0INT for Linux (becuase Linux uses it for some reason; maybe due to some initialization).
	cpu_irq_set_enable(70, TRUE);
	cpu_irq_set_handler(70, (cpu_callback) irq_handler);

	if (intc->intc_protection) {
		printf("HYPERVISOR INTC_PROTECTION ACTIVATED: 0x%x\n", intc->intc_protection);
		while (1);
	}

/*
//////////////


//while (1);
#define INTC_IRQ_TIMER0 66
#define INTC_IRQ_TIMER1_MS 67
#define INTC_IRQ_TIMER2 68
#define INTC_IRQ_TIMER3 69
#define INTC_IRQ_TIMER4 92
#define INTC_IRQ_TIMER5 93
#define INTC_IRQ_TIMER6 94
#define INTC_IRQ_TIMER7 95
	cpu_irq_set_enable(INTC_IRQ_TIMER0, TRUE);
	cpu_irq_set_handler(INTC_IRQ_TIMER0, (cpu_callback) irq_handler);
	cpu_irq_set_enable(INTC_IRQ_TIMER1_MS, TRUE);
	cpu_irq_set_handler(INTC_IRQ_TIMER1_MS, (cpu_callback) irq_handler);
	cpu_irq_set_enable(INTC_IRQ_TIMER3, TRUE);
	cpu_irq_set_handler(INTC_IRQ_TIMER3, (cpu_callback) irq_handler);
	cpu_irq_set_enable(INTC_IRQ_TIMER4, TRUE);
	cpu_irq_set_handler(INTC_IRQ_TIMER4, (cpu_callback) irq_handler);
	cpu_irq_set_enable(INTC_IRQ_TIMER5, TRUE);
	cpu_irq_set_handler(INTC_IRQ_TIMER5, (cpu_callback) irq_handler);
	cpu_irq_set_enable(INTC_IRQ_TIMER6, TRUE);
	cpu_irq_set_handler(INTC_IRQ_TIMER6, (cpu_callback) irq_handler);
	cpu_irq_set_enable(INTC_IRQ_TIMER7, TRUE);
	cpu_irq_set_handler(INTC_IRQ_TIMER7, (cpu_callback) irq_handler);
//////////////
*/

	/*Enable interrupts for Linux UART0 */
	cpu_irq_set_enable(72, TRUE);
	cpu_irq_set_handler(72, (cpu_callback) irq_handler);

	intc->intc_control = INTC_CONTROL_NEWIRQAGR;
}
