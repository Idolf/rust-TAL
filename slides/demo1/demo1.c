void fiboloop(int a, int b) {
  while(1) {
    int tmp = a;
    a += b;
    b = tmp;
  }
}
