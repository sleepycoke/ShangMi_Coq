Require Import BinPosDef.
Require Import Arith.
Require Import NArith.
Require Import Ascii String.
Require Import Coq.Strings.HexString.


Module notation_mod. 
Definition testop := N.succ_double.
Section notation_sec.
Variable op : N -> bool. 

Notation "- x" := (op x).
Compute - 3%N.
End notation_sec.
Print testop. 
End notation_mod. 

Class ECF : Type := mkField {U : Type; wrp : N -> U; uwp : U -> N;
    id0 : U; id1 : U; eql : U -> U -> bool; opp : U -> U;
       inv : U -> U; add : U -> U -> U; sub : U -> U -> U;
         mul : U -> U -> U; div : U -> U -> U; dbl : U -> U;
           squ : U -> U; pow : U -> N -> U}.
            
Print ECF.
Notation "x + y" := (add x y).
Print "+". 
