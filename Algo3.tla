-------------------------------- MODULE Algo3 --------------------------------
EXTENDS TLC,Integers
CONSTANTS v

(*
--algorithm  Algo3 {
variables a,b,c,i,r;
{
     a:=1;
     b:=1;
     i:=2;
     if(x==0 or x==1){
        r:=1;
     }else{
        while(i-1 < x)
        {
            i:=i+1;
            c:=a;
            a:=b;
            b:=2*c+2*b;
        }
        r:=b;
    }
}

}

*)

======================