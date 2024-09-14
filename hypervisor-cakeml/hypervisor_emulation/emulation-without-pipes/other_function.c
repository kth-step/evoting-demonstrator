#include <stdio.h>
#include <stdint.h>

//void (* transfer_function(void (*)(int)))(uint64_t);
/*
void (* rust_function(void *address))(uint64_t);
void (* cakeml_function(void *address))(uint64_t);

void (* rust_function(void *address))(uint64_t) {
	printf("rust_function: address = 0x%p, address = 0xlX\n", address, (uint64_t) address);
	return &cakeml_function;
}

void (* cakeml_function(void *address))(uint64_t) {
	printf("cakeml_function: address = 0x%p, address = 0xlX\n", address, (uint64_t) address);
	return &rust_function;
}
*/

//gcc other_function.c cakeml_to_rust.S ../linuxapp/rust_to_cakeml.S
//gcc -Wl,-Map,layout.map other_function.c cakeml_to_rust.S ../linuxapp/rust_to_cakeml.S
//nm -S a.out

extern uint64_t cakeml_sp;
extern uint64_t cakeml_bp;

extern void cakeml_to_rust(uint64_t);
extern void rust_to_cakeml(uint64_t);

void cakeml(void);
void rust(uint64_t);

uint64_t counter = 0;

uint64_t cake2rust(uint64_t rust_address) {
	cakeml_to_rust(rust_address);
	asm volatile("movq %%rdi, %0" : "=r" (rust_address) : :);
	return rust_address;
}

uint64_t rust2cake(uint64_t cake_address) {
	rust_to_cakeml(cake_address);
	asm volatile("movq %%rdi, %0" : "=r" (cake_address) : :);
	return cake_address;
}

void cakeml(void) {
	uint64_t raddress;
	asm volatile("movq %%rdi, %0" : "=r" (raddress) : :);	//MUST STORE THE RUST RETURN ADDRESS AT ENTRY, LOCATED IN RDI.

	counter++;
	printf("cake1: counter = %lu\n", counter);
	printf("cakeml1: 0x%lX\n", raddress);


	counter++;
	printf("cake2: counter = %lu\n", counter);
	raddress = cake2rust(raddress);

	counter++;
	printf("cake3: counter = %lu\n", counter);



	printf("cakeml2: 0x%lX\n", raddress);


	counter++;
	printf("cake4: counter = %lu\n", counter);
	raddress = cake2rust(raddress);
	counter++;
	printf("cake5: counter = %lu\n", counter);



	printf("cakeml3: 0x%lX\n", raddress);

	counter++;
	printf("cake6: counter = %lu\n", counter);
}

void rust(uint64_t caddress) {
	uint64_t rsp;
	uint64_t rspv;
	uint64_t rbp;

	counter++;
	printf("rust1: counter = %lu\n", counter);


	asm volatile("movq %%rsp, %0" : "=r" (rsp) : :);

	asm volatile("movq 0x18(%%rsp), %0" : "=r" (rspv) : :);
	printf("rustsp: 0x%lX, 0x%lX\n", rsp, rspv);
	asm volatile("movq %%rbp, %0" : "=r" (rbp) : :);
	printf("rustbp: 0x%lX\n", rbp);

	printf("rust1: 0x%lX\n", caddress);

	counter++;
	printf("rust2: counter = %lu\n", counter);


	caddress = rust2cake(caddress);


	counter++;
	printf("rust3: counter = %lu\n", counter);


	printf("rust2: 0x%lX\n", caddress);
	asm volatile("movq %%rbp, %0" : "=r" (rbp) : :);
	printf("rustbp: 0x%lX\n", rbp);


	counter++;
	printf("rust4: counter = %lu\n", counter);
	caddress = rust2cake(caddress);

	counter++;
	printf("rust5: counter = %lu\n", counter);

	printf("rust3: 0x%lX\n", caddress);


	asm volatile("movq %%rsp, %0" : "=r" (rsp) : :);
	asm volatile("movq 0x18(%%rsp), %0" : "=r" (rspv) : :);
	asm volatile("movq %%rbp, %0" : "=r" (rbp) : :);
	printf("rustsp: 0x%lX, 0x%lX\n", rsp, rspv);
	printf("rustbp: 0x%lX\n", rbp);
	counter++;
	printf("rust6: counter = %lu\n", counter);
}

void main(void) {
	uint64_t caddress;
	uint64_t rsp;
	uint64_t rbp;

	printf("main1: counter = %lu\n", counter);

	asm volatile("movq %%rsp, %0" : "=r" (rsp) : :);
	asm volatile("movq %%rsp, %0" : "=r" (rbp) : :);
	printf("main, rustsp1: 0x%lX\n", rsp);
	printf("main, rustbp1: 0x%lX\n", rbp);
	cakeml_sp = rsp - 1024*1024;
	cakeml_bp = rbp - 1024*1024;
	printf("&cakeml_sp = 0x%p, &cakeml_bp = 0x%p\n", &cakeml_sp, &cakeml_bp);
	printf("cakeml_sp = 0x%lX, cakeml_bp = 0x%lX\n", cakeml_sp, cakeml_bp);
	asm volatile("lea cakeml(%%rip), %0" : "=r" (caddress) : :);

	counter++;
	printf("main2: counter = %lu\n", counter);
	rust(caddress);

	asm volatile("movq %%rsp, %0" : "=r" (rsp) : :);
	asm volatile("movq %%rbp, %0" : "=r" (rbp) : :);
	printf("main, rustsp2: 0x%lX\n", rsp);
	printf("main, rustbp2: 0x%lX\n", rbp);
	counter++;
	printf("main3: counter = %lu\n", counter);
}
