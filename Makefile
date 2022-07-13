all: bce

bce: bce.c
	gcc bce.c -std=c99 -O2 -o bce

clean:
	rm bce
