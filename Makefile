
FLAGS = -Wall -Wextra

all: test

test: test.c tweetnacl.c
	gcc $(FLAGS) -g -o test test.c tweetnacl.c

tweetnacl.o: tweetnacl.c tweetnacl.h
	gcc -c -Wall -Wextra tweetnacl.c

clean:
	rm -rf *.o test test.dSYM
