#include <stdio.h>

int fact(int n)
{
	int f;

	if (n < 2)
		return 1;

	f = fact(n-1);
	return n * f;
}

int fact_sq(int n)
{
	int f;

	f = fact(n*n);
	return f;
}

int main()
{
	printf("fact    4 = %d\n", fact(4));
	printf("fact_sq 4 = %d\n", fact_sq(4));
	return 0;
}
