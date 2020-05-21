Require Export SMlib.
(* A simple linear congruential generator. Can not generate all elements in F_m *)
(* However, due to Hull-Dobell Theorem, to generate all elements,
  * the multiplier must be 1 if the increment is not zero *)
Definition LCG_31 (m x : N) : N :=
  (x * 3 + 1) mod m.  
(* Guaranteed to generate all elements but too trivial *)
Definition LCG_13 (m x : N) : N :=
  (x + 3) mod m.
