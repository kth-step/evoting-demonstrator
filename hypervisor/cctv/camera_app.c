#include <stdio.h>		//For printing and file accesses.
#include <stdint.h>		//For uint32_t.
#include <time.h>		//For time_t, time() and local_time().
#include <string.h>		//For memset.

#define X	320
#define Y	240
#define BMP_HEADER_SIZE 66
#define BUFFER_SIZE (2*X*Y + BMP_HEADER_SIZE)
static uint8_t buffer[BUFFER_SIZE];

uint32_t invoke_cctv(void) {
	uint32_t result;

	asm volatile("mov r0, %0" : : "r" ((uint32_t) buffer) : "r0");
	asm volatile("mov r1, %0" : : "r" ((uint32_t) BUFFER_SIZE) : "r1");
	asm volatile("mov r7, #449" : : : "r7");		//Syscall number.
	asm volatile("svc 0x00000000" :::);				//System call.
	asm volatile("mov %0, r0" : "=r" (result) : :);	//Reads result.

	return result;
}

void getnowtime(char *nowtime) {
	char sec[2];
	char min[2];
	char hour[2];
	char day[2];
	char mon[2];
	char year[4];
	time_t timep;
	struct tm *p;
	time(&timep);
	p=localtime(&timep);
	memset(nowtime,0,20);

	sprintf(year,"%d",(1900+p->tm_year));
	strcat(nowtime,year);
	if((1+p->tm_mon) < 10)
	strcat(nowtime,"0");
	sprintf(mon,"%d",(1+p->tm_mon));
	strcat(nowtime,mon);
	if(p->tm_mday < 10)
	strcat(nowtime,"0");
	sprintf(day,"%d",p->tm_mday);
	strcat(nowtime,day);
	if(p->tm_hour < 10)
	strcat(nowtime,"0");
	sprintf(hour,"%d",p->tm_hour);
	strcat(nowtime,hour);
	if(p->tm_min < 10)
	strcat(nowtime,"0");
	sprintf(min,"%d",p->tm_min);
	strcat(nowtime,min);
	if(p->tm_sec < 10)
	strcat(nowtime,"0");
	sprintf(sec,"%d",p->tm_sec);
	strcat(nowtime,sec);
	printf("nowtime is %s\n",nowtime);
}

int update_log(char *path) {
	FILE *fp = fopen("/media/usb/tftp_files/cctv.log", "a+");	//Append.
	if (fp == NULL) {
		printf("open log file failed");
		return -4;
	}
	fprintf(fp, "%s\n", path);
	fclose(fp);
	return 0;
}

int store_file(void) {
	char filePath[50];
	char nowtime[20];
	//Construct a file name
	memset(filePath, 0, 50);
	strcat(filePath, "/media/usb/tftp_files/cctv_photo");
	getnowtime(nowtime);
	strcat(filePath, nowtime);
	strcat(filePath, ".bmp");
	//Open the new file
	FILE *fp = fopen(filePath, "wb+");	//Write binary.

	if (fp == NULL) {
		printf("open file failed");
		return -1;
	}
	if (fwrite(buffer, 1, BUFFER_SIZE, fp) < BUFFER_SIZE) {
		printf("could not write all pixels to the file\n");
		return -2;
	}
	if (fclose(fp)) {
		printf("could not close file\n");
		return -3;
	}

	return update_log(filePath);
}

void main(void) {
	uint32_t result = invoke_cctv();
	uint32_t ret = store_file();
	if (!ret)
		printf("Successful file write\n");

	printf("Hypervisor returns: 0x%X\n", result);
}
