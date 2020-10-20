Require Export Coq.PArith.BinPosDef. 
Require Export Coq.ZArith.BinIntDef.  
Require Export Coq.Strings.BinaryString. 
Require Export Coq.Strings.HexString. 
Require Export Ascii String. 
Require Export Coq.Strings.Ascii. 
Require Export Coq.Strings.String. 
Require Export Coq.Lists.List.
Require Export NArith.
Require Export Psatz.

Print nat. 
Class Eql (A : Type) (add : A -> A -> A) := mkeql {eqb : A -> A -> bool}.
Instance natEql : Eql nat := {eqb := Nat.eqb}.
Instance natEql2 : Eql nat := {eqb := fun _ _ => true}.
Check fun _ _ => true. 
Definition boolEql : Eql bool := mkeql bool (fun (_ _ : bool) => true).

Definition testnateqb {natEq : Eql nat}(x y : nat) := @eqb nat natEq x y.
Compute testnateqb 1 2.
Definition testeqb {A : Type}{aEq : Eql A}(x y : A) := eqb x y.
Definition testeqb2 {A : Type}{aEq2 : Eql A}(x : A) := testeqb x x.
Definition testeqb2' {A : Type}{aEq2 : Eql A}(x : A) := @testeqb A aEq2 x x. 
