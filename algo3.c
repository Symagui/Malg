#include <stdio.h>

int p1(int x){
  int a,b,c,i,r,fin;
  a=1;
  b=1;
  i=2;
  if (x==0) {
    r=1;
  } else {
    if (x==1) {
      r=1;
    } else {
      while (i-1 < x){
        i=i+1;
	      c=a;
	      a=b;
	      b=2*c+2*b;
	     }
     }
    r=b;
  }
  return(r);
}



int main(){
  int v;
  printf("Entrez la valeur  pour  v\n");
  scanf("%d", &v);
  printf(" voici la réponse de votre solution p2(%d)=%d\n",v,p1(v));
  return 0;
}
