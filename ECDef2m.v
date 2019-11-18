Require Export DataTypes.

Open Scope list_scope. 
Definition bf_add (x y : bL) : bL :=
  bLXOR x y.

Compute bL2bS (bf_add (bS2bL "") (bS2bL "10011")). 
Compute bL2bS (bf_add (bS2bL "") (bS2bL "")). 

Definition bf_double (x : bL) : bL :=
  match x with
    | [] => []
    | _ => x ++ [false]
  end.   


Fixpoint bf_mul_tail (x y acc : bL) : bL :=
  let acc' := bf_double acc in
    match y with
    | [] => acc
    | false :: t =>
        bf_mul_tail x t acc'
    | true :: t =>
        bf_mul_tail x t (bf_add acc' x)
    end. 

Definition bf_mul_raw (x y : bL) : bL :=
  bf_mul_tail x y [].

Compute bL2bS (bf_mul_raw (bS2bL "11011") (bS2bL "10011")). 
Compute bL2bS (bf_mul_raw (bS2bL "") (bS2bL "10011")). 
Compute bL2bS (bf_mul_raw (bS2bL "10011")(bS2bL "")). 

(* Returns (quotient, remainder) *)
Fixpoint bf_mod_tail (x y r : bL)(ly lr : nat) : bL :=
  let r' := if negb (Nat.leb (length y) (length r)) then bf_add r y else r in
    match x with
    | [] => r'
    | hx :: tx =>
        bf_mod_tail tx y (r' ++ [hx]) (length r') ly
    end.  

Definition bf_mod (x y : bL) : bL :=
  bf_mod_tail x y [] (length y) 0. 
  
Compute bf_mod (bS2bL "110011101") (bS2bL "1101"). 

Close Scope list_scope. 
