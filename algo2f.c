#include <stdio.h>

int main(){
  int array[100], n = -1, c, d, position, swap;
  while (n<1 || n>100){
  printf("Enter number of elements < 100\n");
  scanf("%d",&n);
  }
  printf("Enter %d integers\n",n);

  // Problème si n > 100 ou n<0 ? Pas géré dans l'énoncé
  /*@ loop invariant \valid(array+ (0..n-1));
      loop invariant 0<n<=100; */
  for (c=0; c<n; c++){
    scanf("%d", &array[c]);
  }


  /*@ loop invariant \forall int i,j; (0 < i < c && c < j < n-1) ==> array[i] <= array[j] ;
      loop invariant \forall int i,j; (0 < i < j && j < c) ==> array[i] <= array[j];
      loop invariant 0 <= c < n;
  */
  for (c = 0; c < (n-1); c++){
    position = c;
    /*@ loop invariant \forall int i; c <= i < d ==> array[position] <= array[i];
        loop invariant \forall int i,j; (0 < i < c && c < j < n-1) ==> array[i] <= array[j] ;
        loop invariant \forall int i,j; (0 < i < j && j < c) ==> array[i] <= array[j];
        loop invariant c+1 <= d <= n;
        loop invariant c<=position<n;
        loop assigns d,position; */
    for (d = c+1; d<n; d++){
      if (array[position]>array[d]) position = d;
    }
    //@ assert \forall int i; c<=i<n ==>array[position] <= array[i];
    if (position != c){
      swap = array[c];
      array[c] = array[position];
      //@ assert \forall int i,j; (0 < i < c && c < j < n-1) ==> array[i] <= array[j] ;
      //@ assert \forall int i,j; (0 < i < j && j < c) ==> array[i] <= array[j];
      array[position] = swap;
      //@ assert c<=position<n;
      //@ assert 0 <= c < n;
      //@ assert array[c] <= array[position];
      //@ assert \forall int i; c<=i<n ==>array[c] <= array[i];
      //@ assert \forall int i,j; (0 < i < c && c < j < n-1) ==> array[i] <= array[j] ;
      //@ assert \forall int i,j; (0 < i < j && j < c) ==> array[i] <= array[j];
      
    }
    // assert \forall int i,j; (0 < i < j && j < c) ==> array[i] <= array[j];
  }
  //@ assert \forall int i,j; (0 < i < j && j < n-1) ==> array[i] <= array[j] ;
  printf("Sorted list in ascending order :\n");
  for (c=0; c<n; c++){
    printf("%d\n",array[c]);
  }

  return 0;
}
