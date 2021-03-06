----------------- MODULE algo1 ----------------
EXTENDS Integers, TLC
CONSTANTS n

(*
--algorithm algo1 {

    variables i=3,count,c=2,nbprintf=0,lastprintedvalue=2,previouslastprintedvalue=1;
    {
        if (n >= 1) {
            print <<"First ", n, " prime numbers are :">>;
            print <<2>>;
            nbprintf := nbprintf + 1;
        };
        
        count := 2;
        while (count <= n) {
            c := 2;
            while (c <= (i - 1) /\ (i % c) # 0) {
                c := c + 1;
            };
            
            if (c = i) {
                print <<i>>;
                nbprintf := nbprintf + 1;
                previouslastprintedvalue := lastprintedvalue;
                lastprintedvalue := i;
                count := count + 1;
            };
            
            i := i + 1;
        }
    }
}

*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES i, count, c, nbprintf, lastprintedvalue, previouslastprintedvalue, 
          pc

vars == << i, count, c, nbprintf, lastprintedvalue, previouslastprintedvalue, 
           pc >>

Init == (* Global variables *)
        /\ i = 3
        /\ count = defaultInitValue
        /\ c = 2
        /\ nbprintf = 0
        /\ lastprintedvalue = 2
        /\ previouslastprintedvalue = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF n >= 1
               THEN /\ PrintT(<<"First ", n, " prime numbers are :">>)
                    /\ PrintT(<<2>>)
                    /\ nbprintf' = nbprintf + 1
               ELSE /\ TRUE
                    /\ UNCHANGED nbprintf
         /\ count' = 2
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << i, c, lastprintedvalue, previouslastprintedvalue >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF count <= n
               THEN /\ c' = 2
                    /\ pc' = "Lbl_3"
               ELSE /\ pc' = "Done"
                    /\ c' = c
         /\ UNCHANGED << i, count, nbprintf, lastprintedvalue, 
                         previouslastprintedvalue >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF c <= (i - 1) /\ (i % c) # 0
               THEN /\ c' = c + 1
                    /\ pc' = "Lbl_3"
                    /\ UNCHANGED << i, count, nbprintf, lastprintedvalue, 
                                    previouslastprintedvalue >>
               ELSE /\ IF c = i
                          THEN /\ PrintT(<<i>>)
                               /\ nbprintf' = nbprintf + 1
                               /\ previouslastprintedvalue' = lastprintedvalue
                               /\ lastprintedvalue' = i
                               /\ count' = count + 1
                          ELSE /\ TRUE
                               /\ UNCHANGED << count, nbprintf, 
                                               lastprintedvalue, 
                                               previouslastprintedvalue >>
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
                    /\ c' = c

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

max(a, b) == IF a > b THEN a ELSE b
prime(a) == \A x \in 2..a : (x = a \/ a % x # 0)

Pre ==
    /\ pc = "Lbl_1" => n \in Int  (* l'entree n est conforme *)

Post == 
    /\ pc = "Done" /\ n \geq 0 => nbprintf = n  (* le nombre de valeur affichees au total est correct *)
    /\ pc = "Done" /\ n < 0 => nbprintf = 0  (* le nombre de valeur affichees au total est correct *)

Safe ==
    /\ prime(lastprintedvalue) (* les nombres affiches sont premiers *)
    /\ n \geq 0 => (nbprintf \leq n /\ nbprintf \geq 0) (* test du nombre de printf *)
    /\ n < 0 => nbprintf = 0
    /\ lastprintedvalue > previouslastprintedvalue (* les valeurs affichees sont dans l'ordre croissant *)
    /\ lastprintedvalue - previouslastprintedvalue > 1 => (\A x \in previouslastprintedvalue + 1 .. lastprintedvalue - 1 : prime(x) = FALSE) (* aucune valeur entre deux affich�es n'est premier *) 
   
Exec == 
    /\ n \geq 1 => (count \leq n + 1 /\ count \geq 0) (* limites de count entre 0 et n + 1 *)
    /\ n \leq 0 => (count \geq 0 /\ count \leq 2)
    /\ c \leq i /\ c \geq 1 (* limites de c entre 1 et i *)
    /\ i \geq 3 /\ i \in Nat (* i ne d�passe pas la limite des entiers *)
    
================================================



























