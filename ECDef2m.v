Require Export DataTypes.

Open Scope list_scope. 

Fixpoint removeleading0s (x : bL) : bL :=
  match x with
  | false :: t => removeleading0s t
  | _ => x
  end. 

Compute removeleading0s [false; false; true; true; false]. 

Definition bf_bL_add (x y : bL) : bL :=
  removeleading0s (bLXOR x y).

Definition bf_add (x y : N) : N :=
  N.lxor x y.

Compute bf_add 7 2. 
Compute bf_add 2 7. 

Compute bL2bS (bf_bL_add (bS2bL "") (bS2bL "10011")). 
Compute bL2bS (bf_bL_add (bS2bL "") (bS2bL "")). 

Definition bf_bL_double (x : bL) : bL :=
  match x with
    | [] => []
    | _ => x ++ [false]
  end.   

(* Returns remainder *)
Fixpoint bf_bL_mod_tail (x y r : bL)(ly : nat) : bL :=
  let r' := if (Nat.leb (ly) (length r)) then bf_bL_add r y else r in
    match x with
    | [] => r'
    | hx :: tx =>
        bf_bL_mod_tail tx y (r' ++ [hx]) ly 
    end.  

Definition bf_bL_mod (x y : bL) : bL :=
  bf_bL_mod_tail x y [] (length y). 
  

Open Scope positive_scope. 
Fixpoint bf_mod_pos (x y : positive)(ly : nat) : N :=
  match x with
  | 1 => 
    match y with
    | 1 => 0
    | _ => 1
    end
  | p~0 | p~1 =>
      let r'2 := N.double (bf_mod_pos p y ly) in 
      let r := if even (Npos x) then r'2 else (r'2 + 1)%N in
      if (Nat.eqb (size_nat r) ly) then bf_add r (Npos y) else r
  end. 

Definition bf_mod (x y : N) : N :=
  match x, y with
  | N0, _ => N0
  | _, N0 => x
  | pos xp, pos yp => 
      bf_mod_pos xp yp (size_nat y)
  end. 

Fixpoint bf_bL_mul_tail (x y acc : bL) : bL :=
  let acc' := bf_bL_double acc in
    match y with
    | [] => acc
    | false :: t =>
        bf_bL_mul_tail x t acc'
    | true :: t =>
        bf_bL_mul_tail x t (bf_bL_add acc' x)
    end. 

Open Scope positive_scope. 
Fixpoint bf_mul_pos (x : positive)(y : N) : N :=
  match x with
  | 1 => y
  | p~0 => N.double (bf_mul_pos p y) 
  | p~1 => bf_add y (N.double (bf_mul_pos p y))
  end. 
Close Scope positive_scope. 

Definition bf_mul (x y g : N) : N :=
  match x with
  | 0 => 0
  | Npos p => bf_mod (bf_mul_pos p y) g
  end.

Definition bf_bL_mul_raw (x y : bL) : bL :=
  bf_bL_mul_tail x y [].

(*
Compute bL2bS (bf_bL_mul_raw (bS2bL "11011") (bS2bL "10011")). 
Compute N2bS (bf_mul (bS2N "11011") (bS2N "10011")). 
Compute bL2bS (bf_bL_mul_raw (bS2bL "") (bS2bL "10011")). 
Compute N2bS (bf_mul (bS2N "") (bS2N "10011")). 
Compute bL2bS (bf_bL_mul_raw (bS2bL "10011")(bS2bL "")). 
Compute N2bS (bf_mul (bS2N "10011")(bS2N "")). 
*)
Compute N2bS (bf_mul (bS2N "11011") (bS2N "10011") (bS2N "100101")). 

Close Scope positive_scope. 

(* Test whether (x, y) is on the elliptic-curve defined by a b g *)
(*
Definition OnCurve2m (x y g a b : N) : bool := 
  ((N.square y) mod p =? ((power x 3 p) + a * x + b) mod p). 
*)


Compute bL2bS (bf_bL_mod (bS2bL "110011101") (bS2bL "100101")). 
Compute N2bS (bf_mod (bS2N "110011101") (bS2N "100101")). 

Close Scope list_scope. 
