------------------------------- MODULE Algo3 -------------------------------

EXTENDS Naturals, TLC

VARIABLES array, n, c, d, swap, pos, pc

Sorted(a) == \A i \in 1..n-1 (* 100 ?*) : a[i] <= a[i+1]
ArraySorted == { a \in 1..n-1 : Sorted(a)}

\* BEGIN TRANSLATION

vars == << array, n, c, d, swap, pos, pc >>

Init == /\ array \in ArraySorted
        /\ n =< 100
        /\ c = 0
        /\ d = 1
        /\ pos = 0
        /\ pc = "Debut"
      
      
Echange == /\ pc = "Echange"
         /\ IF (c < (n-1))
         THEN /\ pos' = c /\ d = c+1 
              /\ IF d < n
              THEN IF (array[pos] > array[d]) 
                   THEN /\ pos = d /\ d'=d+1
              IF (pos <> c) THEN /\ swap' = array[c]
                   /\ array[c]' = array[pos]
                   /\ array[pos]' = swap'
                   /\ n' = n
         /\ c' = c+1 /\ n' = n /\ d' = d  /\ pc' = "Echange"
         ELSE Assert(ArraySorted) /\ UNCHANGED(array,n,c,d,swap,pos) /\ pc' = "Fin" 
         
         
         
         IF (pos <> pos')
            THEN /\ array[c] = array[pos]

Next == Echange \/ (pc = "Fin" /\ UNCHANGED(array,n,c,d,swap,pos))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Fin")

\* END TRANSLATION