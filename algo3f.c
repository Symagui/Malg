#include <stdio.h>
#include <limits.h>
int inmax = INT_MAX;
/*@
axiomatic Solve {
  logic integer solve(integer n);

  axiom solve_0: solve(0) ==  1;

  axiom solve_1: solve(1) ==  1;

  axiom solve_n: \forall integer n;  n>1 ==> solve(n) == 2*solve(n-2)+2*solve(n-1);
}*/


/*@ 
requires 0 <= x <= 24;
ensures \result > 0;
ensures \result == solve(x);
*/
int p1(int x){
  int a,b,c,i,r,fin;
  a=1;
  b=1;
  i=2;
  if (x==0) {
    r=1;
  } else if (x==1) {
    r=1;
  } else {
		//@ assert x <= 24;
		//@ loop invariant a>0 && b>0 && b == solve(i-1);
    while (i-1 < x){
			//@ assert i <= x;
      i=i+1;
	    c=a;
	    a=b;
	    b=2*c+2*b;
			printf("%d\n", b);
	  }
  	r=b;
  }
  return(r);
}


/*@ 
		ensures \result == 0;
*/
int main(){
  int v = -1;
	while (v < 0 || v >= 25){
  	printf("Entrez la valeur  pour  v\n");
  	scanf("%d", &v);
	}
	//@ assert v >= 0 && v< 25;
  printf(" voici la réponse de votre solution p2(%d)=%d\n",v,p1(v));
  return 0;
}
