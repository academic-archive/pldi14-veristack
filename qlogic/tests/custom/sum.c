#include <stdio.h>

int sum(int a[], int lo, int hi)
{
	int s;

	if (hi <= lo)
		return 0;

	s = sum(a, lo+1, hi);
	return a[lo] + s;
}

int main()
{
	int t[] = { 1, 2, 3, -1, -2, 4, -3, 5, -6 };
	int s;

	s = sum(t, 0, sizeof t / sizeof t[0]);

	printf("sum is %d\n", s);
	return 0;
}
