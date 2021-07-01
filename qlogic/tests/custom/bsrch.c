typedef unsigned int u32;

u32 a[1000];

u32 srch(u32 elem, u32 beg, u32 end) {
	u32 mid = beg + (end-beg)/2;

	if (end-beg <= 1) return beg;

	if (a[mid] > elem) end = mid;
	else beg = mid;

	return srch(elem, beg, end);
}
