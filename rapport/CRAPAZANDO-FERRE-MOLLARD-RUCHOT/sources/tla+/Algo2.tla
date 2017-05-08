---------------------------- MODULE algo2 ----------------------------
EXTENDS Naturals, TLC
CONSTANTS nhat
(*
--algorithm algo2{
    variables c, d, position, swap, array;
    {
        c := 0;
        while(c < (n-1)){
            position := c;
            d := c+1;
            while(d < n){
                if(array[position] > array[d]){
                    position := d;
                };
                d := d+1;
            };
            if(position != c){
                swap := array[c];
                array[c] := array[position];
                array[position] := swap;
            };
            c := c+1;
        };
        print<<"Sorted list in ascending order">>;
        c := 0;
        while(c < n){
            print<<array[c]>>;
            c := c+1;
        };
    }
}
*)


\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES c, d, position, swap, array, pc

vars == << c, d, position, swap, array, pc >>

Init == (* Global variables *)
        /\ c = defaultInitValue
        /\ d = defaultInitValue
        /\ position = defaultInitValue
        /\ swap = defaultInitValue
        /\ array = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ c' = 0
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << d, position, swap, array >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF c < (n-1)
               THEN /\ position' = c
                    /\ d' = c+1
                    /\ pc' = "Lbl_3"
                    /\ c' = c
               ELSE /\ PrintT(<<"Sorted list in ascending order">>)
                    /\ c' = 0
                    /\ pc' = "Lbl_6"
                    /\ UNCHANGED << d, position >>
         /\ UNCHANGED << swap, array >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF d < n
               THEN /\ IF array[position] > array[d]
                          THEN /\ position' = d
                          ELSE /\ TRUE
                               /\ UNCHANGED position
                    /\ d' = d+1
                    /\ pc' = "Lbl_3"
                    /\ UNCHANGED << swap, array >>
               ELSE /\ IF position != c
                          THEN /\ swap' = array[c]
                               /\ array' = [array EXCEPT ![c] = array[position]]
                               /\ pc' = "Lbl_4"
                          ELSE /\ pc' = "Lbl_5"
                               /\ UNCHANGED << swap, array >>
                    /\ UNCHANGED << d, position >>
         /\ c' = c

Lbl_4 == /\ pc = "Lbl_4"
         /\ array' = [array EXCEPT ![position] = swap]
         /\ pc' = "Lbl_5"
         /\ UNCHANGED << c, d, position, swap >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ c' = c+1
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << d, position, swap, array >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ IF c < n
               THEN /\ PrintT(<<array[c]>>)
                    /\ c' = c+1
                    /\ pc' = "Lbl_6"
               ELSE /\ pc' = "Done"
                    /\ c' = c
         /\ UNCHANGED << d, position, swap, array >>

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5 \/ Lbl_6
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION4

PreCond == n <= 100
Invariant == c <= n
PostCond ==  pc = "Done" /\ \A i \in 1..n-1 : array[i] <= array[i+1]

======================================================================
