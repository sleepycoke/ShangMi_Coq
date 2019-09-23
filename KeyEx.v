Require Export Signature. 

Definition constant_v := 256%nat. (*According to the examples. *)

(* ceil(x/y) *)
Definition div_ceil_nat (x : nat)(y : nat) : nat :=
  Nat.div (x + y - 1%nat) y. 

(*
Fixpoint f (n : N) :=
  match n with
  | 0 => 1
  | _ => f(pred n)
  end.   

Compute f 5. 
*)
(* TODO Should we imp a general hash_v here? ignored for now *)
(* j = ceil(klen/v) - i, from ceil(klen/v) - 1 to 0 *)
(* i from 1 to ceil(klen/v), ct = N2bL_len 32 i*)
(* TODO though klen/v could be as long as 2^32, I choose to use nat for 
 simplicity, which suffices for the tests, aka 128 klen *)
(* Returns a reversed HaList *)
(* hash_v returns a bL of length v *)
Fixpoint ComputeHaList (j : nat)(i : N)(Z : bL)(hash_v : bL -> bL)
  (acc : list bL){struct j} :=
  let HaList := hash_v (Z ++ (N2bL_len 32 i)) :: acc in
  match j with
  | O => HaList 
  | S j' => 
      ComputeHaList j' (i + 1) Z hash_v HaList
  end. 

(* K = K' || Ha! *)
Fixpoint ComputeK' (HaList' : list bL)(acc : bL) : bL :=
  match HaList' with
  | [] => acc
  | h :: tl => ComputeK' tl (acc ++ h)
  end. 

Definition KDF (Z : bL)(klen : nat)(hash_v : bL -> bL)(v : nat) : bL :=
  let HaList := ComputeHaList ((div_ceil_nat klen v) - 1) 1 Z hash_v [] in
  match HaList with
  | [] => [] (*HaList should not be empty *)
  | HaLast :: tl =>
    let HaiEx := 
      if Nat.eqb (Nat.modulo klen v) 0 then HaLast
      else subList 0 (klen - v * (Nat.div klen v)) HaLast in
      (ComputeK' tl []) ++ HaiEx
  end. 
      
Module test. 
Definition ZA := hS2bL "E4D1D0C3 CA4C7F11 BC8FF8CB 3F4C02A7 8F108FA0 98E51A66 8487240F 75E20F31". 
Definition ZB := hS2bL "6B4B6D0E 276691BD 4A11BF72 F4FB501A E309FDAC B72FA6CC 336E6656 119ABD67". 
Definition xV := hS2bL "47C82653 4DC2F6F1 FBF28728 DD658F21 E174F481 79ACEF29 00F8B7F5 66E40905". 
Definition yV := hS2bL "2AF86EFE 732CF12A D0E09A1F 2556CC65 0D9CCCE3 E249866B BB5C6846 A4C4A295". 

Definition Z := xV ++ yV ++ ZA ++ ZB. 
 
(*55B0AC62 A6B927BA 23703832 C853DED4*)
Compute bL2hS (KDF Z 128 Hash constant_v). (*Correct*)

End test. 



