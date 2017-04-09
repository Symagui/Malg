----------------- MODULE algo1 ----------------
EXTENDS Integers, TLC
CONSTANTS n

(*
--algorithm algo1 {

    variables i=3,count,c;
    {
        if (n >= 1) {
            print <<"First ", n, " prime numbers are :">>;
            print <<2>>;
        };
        
        count := 2;
        while (count <= n) {
            c := 2;
            while (c <= (i - 1) /\ (i % c) # 0) {
                c := c + 1;
            };
            
            if (c = i) {
                print <<i>>;
                count := count + 1;
            };
            
            i := i + 1;
        }
    }
}

*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES i, count, c, pc

vars == << i, count, c, pc >>

Init == (* Global variables *)
        /\ i = 3
        /\ count = defaultInitValue
        /\ c = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF n >= 1
               THEN /\ PrintT(<<"First ", n, " prime numbers are :">>)
                    /\ PrintT(<<2>>)
               ELSE /\ TRUE
         /\ count' = 2
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << i, c >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF count <= n
               THEN /\ c' = 2
                    /\ pc' = "Lbl_3"
               ELSE /\ pc' = "Done"
                    /\ c' = c
         /\ UNCHANGED << i, count >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF c <= (i - 1) /\ (i % c) # 0
               THEN /\ c' = c + 1
                    /\ pc' = "Lbl_3"
                    /\ UNCHANGED << i, count >>
               ELSE /\ IF c = i
                          THEN /\ PrintT(<<i>>)
                               /\ count' = count + 1
                          ELSE /\ TRUE
                               /\ count' = count
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
                    /\ c' = c

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


================================================
