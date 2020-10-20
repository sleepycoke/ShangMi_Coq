Require Export DataTypes. 
Open Scope list_scope. 
(*TODO rename *)
  
(* Binary fields arithmetics *)
Definition B_add (x y : N) : N :=
  N.lxor x y.
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

(* TODO Consider speeding up *)
Definition Bp_sq_raw (x : N) :=
  Bp_mul_raw x x. 

Definition Bp_sq (gp x : N) :=
  Bp_mul gp x x. 

(* cube *)
Definition Bp_cb (gp x : N) :=
  Bp_mul gp x (Bp_sq gp x). 

(* Polynomial Base *)
(*Definition Bp_pow (m : N)(gp : N)(g : N)(a : N) : N :=
  power_general g a (N.shiftl 1 m)(Bp_sq gp)(Bp_mul gp). 

Definition Bp_inv (m gp g : N) : N :=
  Bp_pow m gp g ((N.shiftl 1 m) - 2).

Definition Bp_div (m gp x y : N) : N :=
  Bp_mul gp x (Bp_inv m gp y). *)



(*Lemma id0_inrng (po : prime_order) : 0 < order po. 
Proof.
destruct po as [p H]. 
simpl. inversion H.
assert (h : 0 < 3). { reflexivity. }
apply (lt_trans 0 3 p h (gt_lt p 3 H)).
Qed.    

Lemma id1_inrng (po : prime_order) : 1 < order po. 
Proof.
destruct po as [p H]. 
simpl. inversion H.
assert (h : 1 < 3). { reflexivity. }
apply (lt_trans 1 3 p h (gt_lt p 3 H)).
Qed.    

Definition id0_builder_pf (po : prime_order) : Fpe po :=
  mkFpe po 0 (id0_inrng po). 

Definition id1_builder_pf (po : prime_order) : Fpe po :=
  mkFpe po 1 (id1_inrng po). 
  *)
