#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>
#include <signal.h>


int cid = 0;

void sigint_handler()
{
  if (cid > 0) {
    printf("killing child process %d\n", cid);
    exit(0);
  }
}

void main(int argc, char *argv[]) {
  char path[256];

  if (getcwd(path, sizeof(path)) == NULL) {
    perror("error executing getcwd()");
  }
  printf("[c main] the current working directory is: %s\n", path);


	int rust_to_cake[2];	//rust_to_cake[0] is for cake (read), rust_to_cake[1] is for rust (write).
	int cake_to_rust[2];	//cake_to_rust[0] is for rust (read), cake_to_rust[1] is for cake (write).
	pipe(rust_to_cake);
	pipe(cake_to_rust);

    pid_t pid = fork();
	if (pid == 0) {							//Child.
		int rust_r, rust_w;						//File descriptors for rust to write and read.
		close(rust_to_cake[0]);					//Close the read end of rust_to_cake pipe.
		close(cake_to_rust[1]);					//Close the write end of cake_to_rust pipe.
		rust_r = dup(cake_to_rust[0]);
		close(cake_to_rust[0]);					//Close the now unused read end of cake_to_rust pipe.
		rust_w = dup(rust_to_cake[1]);
		close(rust_to_cake[1]);					//Close the now unused write end of the rust_to_cake pipe.
  		printf("Rust: rust_r = %d, rust_w = %d\n", rust_r, rust_w);

		//ASSUME FILE DESCRIPTOR INDEXES DO NOT EXCEED 32 BITS IN SIZE.
		char rust_r0 = (char) (rust_r & 0xF);
		char rust_r1 = (char) ((rust_r & 0xF0) >> 8);
		char rust_r2 = (char) ((rust_r & 0xF00) >> 16);
		char rust_r3 = (char) ((rust_r & 0xF000) >> 24);

		char rust_w0 = (char) (rust_w & 0xF);
		char rust_w1 = (char) ((rust_w & 0xF0) >> 8);
		char rust_w2 = (char) ((rust_w & 0xF00) >> 16);
		char rust_w3 = (char) ((rust_w & 0xF000) >> 24);

        int pipe_argc = 9;
		char *pipe_argv[] = {&rust_r0, &rust_r1, &rust_r2, &rust_r3, &rust_w0, &rust_w1, &rust_w2, &rust_w3, NULL};

        int num_elems = argc + pipe_argc;
        char * exec_argv[num_elems];

        for (int i = 0; i < argc; i++) {
          exec_argv[i] = argv[i];
        }
        for (int i = 0; i < pipe_argc; i++) {
          exec_argv[i+argc] = pipe_argv[i];
        }

		execv("./rust_app", exec_argv);
	} else {									//Parent.

      cid = (intmax_t) pid;
      signal(SIGINT, sigint_handler);

		int cake_r, cake_w;						//File descriptors for cake to write and read.
		close(cake_to_rust[0]);					//Close the read end of cake_to_rust pipe.
		close(rust_to_cake[1]);					//Close the write end of rust_to_cake pipe.
		cake_r = dup(rust_to_cake[0]);
		close(rust_to_cake[0]);					//Close the now unused read end of cake_to_rust pipe.
		cake_w = dup(cake_to_rust[1]);
		close(cake_to_rust[1]);					//Close the now unused write end of the rust_to_cake pipe.
  		printf("Cake: cake_r = %d, cake_w = %d\n", cake_r, cake_w);

		char cake_r0 = (char) (cake_r & 0xF);
		char cake_r1 = (char) ((cake_r & 0xF0) >> 8);
		char cake_r2 = (char) ((cake_r & 0xF00) >> 16);
		char cake_r3 = (char) ((cake_r & 0xF000) >> 24);

		char cake_w0 = (char) (cake_w & 0xF);
		char cake_w1 = (char) ((cake_w & 0xF0) >> 8);
		char cake_w2 = (char) ((cake_w & 0xF00) >> 16);
		char cake_w3 = (char) ((cake_w & 0xF000) >> 24);

		char *args[] = {&cake_r0, &cake_r1, &cake_r2, &cake_r3, &cake_w0, &cake_w1, &cake_w2, &cake_w3, NULL};
		// set working directory
        printf("[c main] setting cwd to: %s\n", path);
        chdir(path);
		execv("./cake_app", args);
	}
}
