#include <stdio.h>
#include <stdlib.h>

int *filter_pos(int a[], int *sz, int lo, int hi)
{
	int *b, n;

	if (hi <= lo) {
		b = malloc(*sz * sizeof(int));
		return b;
	}

	if (a[lo] > 0) {
		n = *sz;
		(*sz)++;
		b = filter_pos(a, sz, lo+1, hi);
		b[n] = a[lo];
	} else {
		b = filter_pos(a, sz, lo+1, hi);
	}

	return b;
}

int main()
{
	int t[] = { 1, 2, 3, -1, -2, 4, -3, 5, -6 };
	int *out, i, sz = 0;

	out = filter_pos(t, &sz, 0, sizeof t / sizeof t[0]);

	for (i = 0; i < sz; i++)
		printf("%d ", out[i]);
	puts("");
	return 0;
}
