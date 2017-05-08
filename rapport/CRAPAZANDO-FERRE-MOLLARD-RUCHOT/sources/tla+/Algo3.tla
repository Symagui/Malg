-------------------------------- MODULE Algo3 --------------------------------
EXTENDS TLC,Integers, Reals

(*
--algorithm  Algo3 {
variables a,b,c,i,r;
{
     a:=1;
     b:=1;
     i:=2;
     if(x==0){
        r:=1;
     }else{
        if(x==1){
            r:=1;
        }else{
            while(i-1 < x)
            {
                i:=i+1;
                c:=a;
                a:=b;
                b:=2*c+2*b;
            };
            r:=b;
        }
    }
}

}

*)

\* BEGIN TRANSLATION
CONSTANT x
VARIABLES a, b, c, i, r, pc

vars == << a, b, c, i, r, pc >>

Init == (* Global variables *)
        /\ a = 1
        /\ b = 1
        /\ c = 0
        /\ r = 0
        /\ i = 2
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ a' = 1
         /\ b' = 1
         /\ i' = 2
         /\ IF x=0
               THEN /\ r' = 1
                    /\ pc' = "Done"
               ELSE /\ IF x=1
                          THEN /\ r' = 1
                               /\ pc' = "Done"
                          ELSE /\ pc' = "Lbl_2"
                               /\ r' = r
         /\ c' = c

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i-1 < x
               THEN /\ i' = i+1
                    /\ c' = a
                    /\ a' = b
                    /\ b' = 2*c'+2*b
                    /\ pc' = "Lbl_2"
                    /\ r' = r
               ELSE /\ r' = b
                    /\ pc' = "Done"
                    /\ UNCHANGED << a, b, c, i >>

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

---------------------------------------------

PreCond ==
    /\ pc = "Lbl_1" => (x \leq 24 /\ x >= 0)

TestPreLoop == i>2 \/ b = 1 \* On a pas commencé la boucle donc b=1
TestPostLoop == i\leq2 \/ b = 2*c+2*a \* On a commencé la boucle donc b= 2*c + 2*a

PostCond ==
    /\ pc = "Done" => ( (x\leq1 /\ r=1) \/ (x>1 /\ r=2*c+2*a) ) \*Terminé donc soit c'est pas passé dans la boucle et c'est 1 soit c'est la formule récursive

======================
