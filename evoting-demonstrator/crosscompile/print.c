#ifdef UBUNTU
#include <stdint.h>		//For uint32_t.
#else
#include <stdint-gcc.h>		//For uint32_t.
#endif
#include <stdbool.h>	//For true and false.
#include <stdarg.h>		//For variable number of arguments to printf.
#define UART_LSR_TX_FIFO_E (1UL << 5)
#define UART_LCR_LENGTH_8 ( 3UL << 0)
#define UART_LCR_STOP_1  (0UL << 2)
#define UART_LCR_MODE_OP 0
#define UART_LCR_DIV_EN (1UL << 7)
#define UART_OP_FLAGS  (UART_LCR_MODE_OP | UART_LCR_STOP_1 | UART_LCR_LENGTH_8)
#define LCR	(*((volatile uint32_t *) (0x44E09000 + 0xB5000000 + 4*3)))
#define LSR	(*((volatile uint32_t *) (0x44E09000 + 0xB5000000 + 4*5)))
#define RHR	(*((volatile uint32_t *) (0x44E09000 + 0xB5000000 + 4*0)))

int stdio_can_write(void) {
	if ((LCR & UART_LCR_DIV_EN))
		LCR = UART_OP_FLAGS;

	return (LSR & UART_LSR_TX_FIFO_E) ? true : false;
}

void stdio_write_char(int c)
{
	while (!stdio_can_write());

	RHR = c;

	if (c == '\n') {
		while (!stdio_can_write());
		RHR = '\r';
	}
}

void printf_putchar(char c)
{
	stdio_write_char(c);
}

void printf_string(char *str)
{
	while (*str)
		printf_putchar(*str++);
}

void printf_int(int i)
{
	int f = 0, neg = 0;
	char buffer[12];

	if (i < 0) {
		neg++;
		i = -i;
	}
	do {
		buffer[f++] = '0' + (i % 10);
		i /= 10;
	} while (i);

	if (neg)
		buffer[f++] = '-';

	while (f) {
		printf_putchar(buffer[--f]);
	}
}

void printf_hex(uint32_t n, uint32_t size)
{
	int h;
	int i = 32 / 4 - 1;

	do {
		h = (n >> 28);
		n <<= 4;
		if (size == 2 && i >= 2)
			continue;
		if (h < 10)
			h += '0';
		else
			h += 'A' - 10;

		printf_putchar(h);
	} while (i--);
}

void printf_bin(uint32_t n)
{
	int i;
	for (i = 32; i != 0; i--) {
		if ((i != 32) && !(i & 3))
			printf_putchar('_');
		printf_putchar((n & 0x80000000) ? '1' : '0');
		n <<= 1;
	}
}

void printf_(const char *fmt, ...)
{
	int c;
	va_list args;

	va_start(args, fmt);

	for (;;) {
		c = *fmt;
		if (c == '\0')
			goto cleanup;

		fmt++;
		if (c == '%') {
			c = *fmt;
			fmt++;

			if (c == '\0') {
				printf_putchar(c);
				goto cleanup;
			}

			switch (c) {

			case 'c':
				printf_putchar(va_arg(args, int));
				break;

			case 's':
				printf_string(va_arg(args, char *));
				break;
			case 'i':
			case 'd':
				printf_int(va_arg(args, int));
				break;

			case 'x':
				printf_hex(va_arg(args, uint32_t), 8);
				break;
			case '2':
				printf_hex(va_arg(args, uint32_t), 2);
				break;

			case 'b':
				printf_bin(va_arg(args, uint32_t));
				break;

			case '%':
				printf_putchar(c);
				break;
			default:
				printf_putchar('%');
				printf_putchar(c);
			}

		} else
			printf_putchar(c);
	}

 cleanup:
	va_end(args);
}
