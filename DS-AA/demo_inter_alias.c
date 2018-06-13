void foo(int *p) {
	*p = 10;
}
int main() {
	int a = 0;
	int c;
	int *pa = &a;
	foo(pa);
	c = *pa;
	return 0;
}
