#include <stdio.h>

int main(){
  int array[100], n = -1, c, d, position, swap;
  while (n<1 || n>100){
  printf("Enter number of elements < 100\n");
  scanf("%d",&n);
  }
  printf("Enter %d integers\n",n);

  // On s'assure que l'on a que 100 elements
  /*@ loop invariant \valid(array+ (0..n-1));
      loop invariant 0<n<=100; */
  for (c=0; c<n; c++){
    scanf("%d", &array[c]);
  }

  //A chaque iteration, un element de plus est trie, c'est ce que l'on montre avec le premier invariant
  /*@ loop invariant \forall int i,j; (0 <= i < j < n && i < c) ==> array[i] <= array[j];
      loop invariant 0 <= c < n;
  */
  for (c = 0; c < (n-1); c++){
    position = c;

    /*@ loop invariant \forall int i; c <= i < d ==> array[position] <= array[i];
        loop invariant \forall int i,j; (0 <= i < j < n && i < c) ==> array[i] <= array[j];
        loop invariant c+1 <= d <= n;
        loop invariant c<=position<n;
        loop assigns d,position; */
    for (d = c+1; d<n; d++){
      if (array[position]>array[d]) position = d;
    }

    //@ assert \forall int i; c<=i<n ==>array[position] <= array[i];
    //@ assert \forall int i,j; (0 <= i < j < n && i < c) ==> array[i] <= array[j];

    if (position != c){
      swap = array[c];
      array[c] = array[position];
      //@ assert \forall int i,j; (0 <= i < j < n && i < c) ==> array[i] <= array[j];
      array[position] = swap;
      //On rappelle les assertions après la modification de l'array
      //@ assert array[c] <= array[position];
      //@ assert 0 <= c < n;
      //@ assert \forall int i; c<=i<n ==>array[c] <= array[i];
      //@ assert \forall int i,j; (0 <= i < j < n && i < c) ==> array[i] <= array[j];

    }
  }
  //L'assertion suivante est celle qui prouve le fonctionnement du programme,
  //puisque l'on ne modifie plus le tableau par la suite

  //@ assert \forall int i,j; (0 <= i < j <= n-1) ==> array[i] <= array[j] ;
  printf("Sorted list in ascending order :\n");

  /*@ loop invariant \forall int i,j; (0 <= i < j <= n-1) ==> array[i] <= array[j] ;
      loop invariant 0<= c <= n;*/
  for (c=0; c<n; c++){
    //@ assert c<n-1 ==> array[c] <= array[c+1];
    printf("%d\n",array[c]);
  }

  return 0;
}
