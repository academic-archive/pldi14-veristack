extern int a, b;

int f(void) {
	if (a) {
		a--;
		b++;
		f();
		return 0;
	} else
		return 0;
}
