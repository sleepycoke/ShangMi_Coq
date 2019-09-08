Require Export SM2_SysPara.

Record aaa := mkAAA {abb : nat; bbb : bool}.
Definition aba := {|abb := 1; bbb := true|}. 
Compute aba.
Compute aba.(abb). 

Definition abc := mkAAA 2 false. 

Compute abc.
Compute bbb abc. 
Compute abc.(abb).  

Print N2bL. 

(*5.5 trunk from right *)
(*TODO I reaaly cannot get its definition *)
Definition ENTL (ID : N) :=
  N2bL_len (N.of_nat (List.length (N2BL ID))) 16. 

Open Scope list. 
Definition Z_A (ID_A a b xG yG xA yA : N) :=
  (ENTL ID_A) ++ (N2bL a) ++ (N2bL b) 
    ++ (N2bL xG) ++ (N2bL yG) ++ (N2bL xA) ++ (N2bL yA). 

Definition IDa := hS2N "414C 49434531 32334059 41484F4F 2E434F4D".
Compute IDa. 
Compute List.length (N2BL IDa). 
Compute bL2hS (ENTL IDa).  (*wrong, supposed to be 0090*)
