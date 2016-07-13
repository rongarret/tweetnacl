tweetnacl.o: tweetnacl.c tweetnacl.h
	gcc -c -Wall -Wextra tweetnacl.c

clean:
	rm -f *.o
