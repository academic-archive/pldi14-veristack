#include <stdio.h>
#include <stdlib.h>

#define ALEN 5
int A[ALEN] = { 8, 12, 21, 42, 113 };

int srch(int elem, int beg, int end) {
	int mid = beg + (end-beg)/2;

	if (end-beg <= 1) return beg;

	if (A[mid] > elem) end = mid;
	else beg = mid;

	return srch(elem, beg, end);
}

int *filter_find(int a[], int *sz, int lo, int hi)
{
	int *b, n, in;

	if (hi <= lo) {
		b = malloc(*sz * sizeof(int));
		return b;
	}

	in = srch(a[lo], 0, ALEN);

	if (A[in] == a[lo]) {
		n = *sz;
		(*sz)++;
		b = filter_find(a, sz, lo+1, hi);
		b[n] = a[lo];
	} else {
		b = filter_find(a, sz, lo+1, hi);
	}

	return b;
}

int main()
{
	int t[] = { 8, 2, 3, 42, 12, 4, -3, 5, 113 };
	int *out, i, sz = 0;

	out = filter_find(t, &sz, 0, sizeof t / sizeof t[0]);

	for (i = 0; i < sz; i++)
		printf("%d ", out[i]);
	puts("");
	return 0;
}
