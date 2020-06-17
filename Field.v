Require Export DataTypes. 
Open Scope list_scope. 
(*TODO rename *)

Definition P_add (p x y : N) :=
  (x + y) mod p. 

Definition B_add (x y : N) : N :=
  N.lxor x y.

Definition P_mul (p x y : N) :=
  (x * y) mod p.


Open Scope positive_scope. 
Fixpoint B_mod_pos (x y : positive)(ly : nat) : N :=
  match x with
  | 1 => 
    match y with
    | 1 => 0
    | _ => 1
    end
  | p~0 | p~1 =>
      let r'2 := N.double (B_mod_pos p y ly) in 
      let r := if even (Npos x) then r'2 else (r'2 + 1)%N in
      if (Nat.eqb (size_nat r) ly) then B_add r (Npos y) else r
  end. 

Definition B_mod (x y : N) : N :=
  match x, y with
  | N0, _ => N0
  | _, N0 => x
  | pos xp, pos yp => 
      B_mod_pos xp yp (size_nat y)
  end. 

Fixpoint Bp_mul_pos (x : positive)(y : N) : N :=
  match x with
  | 1 => y
  | p~0 => N.double (Bp_mul_pos p y) 
  | p~1 => B_add y (N.double (Bp_mul_pos p y))
  end. 

Close Scope positive_scope. 

(* Polynomial Base *)
Definition Bp_mul_raw (x y : N) : N :=
  match x with
  | N0 => N0
  | Npos p => Bp_mul_pos p y
  end. 

Definition Bp_mul (gp x y : N) : N :=
  B_mod (Bp_mul_raw x y) gp. 

Definition P_sub (p x y : N) :=
  (p + x - y) mod p.

Definition P_sq (p x : N) :=
  (N.square x) mod p. 

(* TODO Consider speeding up *)
Definition Bp_sq_raw (x : N) :=
  Bp_mul_raw x x. 

Definition Bp_sq (gp x : N) :=
  Bp_mul gp x x. 

(* cube *)
Definition Bp_cb (gp x : N) :=
  Bp_mul gp x (Bp_sq gp x). 
  
(*B.1.1*)
Fixpoint power_tail (g : N)(e : bL)(q : N)(sq : N -> N)
  (mp : N ->  N -> N)(acc : N) : N :=
  match e with
  | [] => acc
  | h :: tl =>
      power_tail g tl q sq mp
      match h with
      | true => (mp (sq acc) g) 
      | false => (sq acc)
      end
  end.

(* Returns g ^ a, q is the size of the field *) 
Definition power_general (g : N)(a : N)(q : N)(sq : N -> N)
  (mp : N -> N -> N)  : N :=
  let e := N.modulo a (q - 1) in
  power_tail g (NtobL e) q sq mp 1. 

Definition P_power (p : N)(g : N)(a : N) : N :=
  power_general g a p (P_sq p) (P_mul p). 

(* Polynomial Base *)
Definition Bp_power (m : N)(gp : N)(g : N)(a : N) : N :=
  power_general g a (N.shiftl 1 m)(Bp_sq gp)(Bp_mul gp). 

(* B.1.2 *)
Definition P_inv (p g : N) :=
  P_power p g (p - 2). 

Definition Bp_inv (m gp g : N) : N :=
  Bp_power m gp g ((N.shiftl 1 m) - 2).

Definition P_div (p : N)(x : N)(y : N) : N :=
  P_mul p x (P_inv p y). 


Definition Bp_div (m gp x y : N) : N :=
  Bp_mul gp x (Bp_inv m gp y). 
