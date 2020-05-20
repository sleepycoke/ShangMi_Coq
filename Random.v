Require Export ECAlg.

(* A simple linear congruential generator. May not generate all elements in F_p *)
Definition LCG_31 (x m : N) : N :=
  (x * 3 + 1) mod m.  

Definition LCG_11 (x m : N) : N :=
  (x + 1) mod m.
