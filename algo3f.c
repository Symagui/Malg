#include <stdio.h>
#include <limits.h>
int inmax = INT_MAX;
/*@
axiomatic Solve {
  logic integer solve(integer n);

  axiom solve_0: solve(0) ==  1;

  axiom solve_1: solve(1) ==  1;

  axiom solve_n: \forall integer n;  (n>1 ==> solve(n) == 2*solve(n-2)+2*solve(n-1)) && (n<0 ==> solve(n) == 1);
}*/


/*@
requires 0 <= x <= 24;
requires \forall int k; 0 <= k <= 1 ==> solve(k) == 1 && 2 <= k < 25 ==> solve(k) == 2*solve(k-1) + 2*solve(k-2);
assigns \nothing;
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
    //Ces invariants sont necessaires pour prouver la formule
		/*@ loop invariant positive : a>0 && b>0;
				loop invariant solvb : b == solve(i-1);
				loop invariant solva : a == solve(i-2);
				loop invariant solvc : i>=3 ==> c == solve(i-3);
				loop invariant i : 2 <= i <= x+1;
				loop assigns a,b,c,i;*/
    while (i-1 < x){
      i=i+1;
	    c=a;
	    a=b;
	    b=2*c+2*b;

	  }
  	r=b;
  }
  //Cette assertion prouve que l'on renvoit le bon resultat
	//@assert solve(x) == r;
  return(r);
}


/*@
		ensures \result == 0;
*/
int main(){
  int v = -1;
  //On verifie que l'utilisateur rentre un nombre valide (0 <= v < 25)
	while (v < 0 || v >= 25){
  	printf("Entrez la valeur  pour  v\n");
  	scanf("%d", &v);
	}
	//@ assert v >= 0 && v< 25;
	int p1v = p1(v);
	//@ assert p1v == solve(v);
  printf(" voici la réponse de votre solution p2(%d)=%d\n",v,p1(v));
  return 0;
}
