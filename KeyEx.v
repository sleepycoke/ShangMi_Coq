Require Export Signature. 

Definition v := 256. (*According to the examples. *)

Print N. 
Print positive. 

Print positive. 
Definition aaa := 2 ^ 32. 



Compute iter aaa (N.add 1) 0 . 

(*
Fixpoint f (n : N) :=
  match n with
  | 0 => 1
  | _ => f(pred n)
  end.   

Compute f 5. 
*)
(* j = ceil(klen/v) - i + 1, from ceil(klen/v) to 0 *)
(* i from 1 to ceil(klen/v) *)
(* TODO though klen/v could be as long as 2^32, I choose to use nat for 
 simplicity, which suffices for the tests, aka 128 klen *)
(* K = K' || Ha! *)
Fixpoint ComputeK' (i j : nat)(Z : bL)(acc : bL){struct j} :=
  match j with
  | O => acc
  | S j' => 




