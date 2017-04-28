#include <stdio.h>

int main(){
  int n, i = 3, count, c;

  /*@ assert i==3; */

  printf("Enter the number of prime numbers required\n");
  scanf("%d",&n);
	
  //On protège n des valeurs négatives pour framac
  if(n<0){
	  n=0;
  }
	
  //On ajoute une variable pour compter le nombre d'affichages total
  int nbprintf = 0;
	
  /*@ assert n>=0; */
  /*@ assert nbprintf==0; */

  if (n>=1){
    printf("First %d prime numbers are :\n", n);
    printf("2\n"); //Preuve 1. Les résultats sont tous des nombes premiers
	//On incrémente nbprintf
	nbprintf++;
  }
  
  //On s'assure qu'on a affiché 2 pour commencer
  /*@ assert n>=1 ==> nbprintf==1; */ //Preuve 2. On a n==nombre de printf
  /*@ assert n<1 ==> nbprintf==0; */ //Preuve 2. On a n==nombre de printf

  
  //Il faut prouver que la boucle termine
  
  /*@ loop invariant 2 <= count;
      loop invariant i>count;
      loop invariant nbprintf<=n;
      loop invariant n>=1 ==> count<=n+1;
      loop invariant n>=1 ==> nbprintf==count-1;
      loop invariant n<1 ==> nbprintf==0;
  */
  for (count = 2; count <= n; ){
    
    /*@ assert count<=n;*/

    /*@ loop invariant 2 <= c <= i;
        loop invariant 2 <= count;
        loop invariant i>count;
        loop invariant nbprintf==count-1;
        loop invariant count<=n;
        loop invariant nbprintf<=n;
        loop invariant c>=3 ==> i%(c-1)!=0;
        loop invariant \forall int w; 2<=w<c ==> i%w!=0;
    */
    for (c = 2; c<= i-1;c++){
      if (i%c == 0) {
        /*@ assert i%c==0; */
        break;
      }
      /*@ assert i%c!=0;*/
    }
    /*@ assert i%c==0 || i==c; */
    /*@ assert \forall int w; 2<=w<c ==> i%w!=0;*/
    /*@ assert count<=n;*/
    /*@ assert nbprintf==count-1;*/

    if (c == i){
      /*@ assert i==c; */
      
      //On prouve que i est premier
      /*@ assert \forall int w; 2<=w<i ==> i%w!=0;*/ //Preuve 1. Les résultats sont tous des nombes premiers
      printf("%d\n",i);
      
	  //On incrémente nbprintf
	  nbprintf++;
      /*@ assert nbprintf==count;*/
      
      count++;
      /*@ assert count<=n+1;*/
      /*@ assert nbprintf==count-1;*/
      /*@ assert nbprintf<=n;*/
    }
    
    i++;
    /*@assert count<=n+1;*/
  }
  /*@ assert count>=n+1; */
  /*@ assert n>=1 ==> count==n+1; */

  //On prouve qu'il y a le bon nombre de résultats
  /*@ assert n>=1 ==> nbprintf==n; */
  /*@ assert n<1 ==> nbprintf==0; */
  /*@ assert n>=0; */

  
  /*@ assert nbprintf==n; */ //Preuve 2. On a n==nombre de printf
  
  return 0;
}
