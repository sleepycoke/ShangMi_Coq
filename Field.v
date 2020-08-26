Require Export DataTypes. 
Open Scope list_scope. 
(*TODO rename *)

(* Primal field arithmetics. *)
Definition P_add (p x y : N) :=
  (x + y) mod p. 

Definition P_mul (p x y : N) :=
  (x * y) mod p.

Definition P_neg (p x : N) :=
  (p - (x mod p)) mod p. 

Definition P_sub (p x y : N) :=
  P_add p x (P_neg p y). 

Definition P_sq (p x : N) :=
  (N.square x) mod p. 
  
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

(* B.1.2 *)
Definition P_inv (p g : N) :=
  P_power p g (p - 2). 
Definition P_div (p : N)(x : N)(y : N) : N :=
  P_mul p x (P_inv p y). 

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
Definition Bp_power (m : N)(gp : N)(g : N)(a : N) : N :=
  power_general g a (N.shiftl 1 m)(Bp_sq gp)(Bp_mul gp). 

Definition Bp_inv (m gp g : N) : N :=
  Bp_power m gp g ((N.shiftl 1 m) - 2).

Definition Bp_div (m gp x y : N) : N :=
  Bp_mul gp x (Bp_inv m gp y). 

(* The order of a primal field, a prime number greater than 3 *)
Record prime_order : Type := mkpo {order : N; gt3 : order > 3 }. 

(* The type of an element of F_p *)
Record Fpe prime_order : Type := 
  mkFpe {val : N; inrng : val < order prime_order}. 
(* The type of an element of F_2m *)
Record Fbe (len : N) : Type := mkFbe {num : N; inlen : N.size num <= len}. 
(*
Inductive Field_Types : Type :=
  | primal : Fpe -> Field_Types
  | binary : Fbe -> Field_Types
. *)
(* U is the type of elements *)

(* U is the type of field elements. id0 is the identity of addition.
id1 is the identity of multiplication. The rest are operators on the field.  *)
Record Field : Type := mkField {U : Type; id0 : U; id1 : U; neg : U -> U; 
  inv : U -> U; add : U -> U -> U; sub : U -> U -> U;
     mul : U -> U -> U; div : U -> U -> U; sq : U -> U;}. 

Lemma id0_inrng (po : prime_order) : 0 < order po. 
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

Lemma mod_inrng (po : prime_order) (a : N) :
  a mod (order po) < (order po).
Proof.
intros. 
destruct po as [p H]. 
assert (H0: p <> 0). {
  inversion H. unfold not. unfold eq. 
  intros. rewrite H0 in H1. inversion H1.      
 }
apply mod_lt. apply H0. 
Qed.

Definition pfe_builder (po: prime_order)(n : N) : Fpe po :=
    mkFpe po (n mod (order po)) (mod_inrng po n). 

Definition pfe_id0_bd (po : prime_order) : Fpe po :=
  pfe_builder po 0. 

Lemma add_inrng (po : prime_order)(x y : Fpe po) : 
  P_add (order po) (val po x) (val po y) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma neg_inrng (po : prime_order)(x : Fpe po) : 
  P_neg (order po) (val po x) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma sub_inrng (po : prime_order)(x y : Fpe po) : 
  P_sub (order po) (val po x) (val po y) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma sq_inrng (po : prime_order)(x : Fpe po) : 
  P_sq (order po) (val po x) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma pw_inrng (po : prime_order)(g a : Fpe po) : 
  P_power (order po) (val po g) (val po a) < (order po). 
Proof. 
  unfold P_power. unfold power_general. unfold power_tail.
  induction (NtobL (val po a mod (order po - 1))) eqn:e_case.  
Admitted. 

Lemma mul_inrng (po : prime_order)(x y : Fpe po) : 
  P_mul (order po) (val po x) (val po y) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma div_inrng (po : prime_order)(x y : Fpe po) : 
  P_div (order po) (val po x) (val po y) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma inv_inrng (po : prime_order)(x : Fpe po) : 
  P_inv (order po) (val po x) < (order po). 
Proof. Admitted. 

Definition po_add (po : prime_order)(x y : Fpe po) : Fpe po :=
    mkFpe po (P_add (order po) (val po x) (val po y)) (add_inrng po x y). 
Definition po_sub (po : prime_order)(x y : Fpe po) : Fpe po :=
    mkFpe po (P_sub (order po) (val po x) (val po y)) (sub_inrng po x y). 
Definition po_mul (po : prime_order)(x y : Fpe po) : Fpe po :=
    mkFpe po (P_mul (order po) (val po x) (val po y)) (mul_inrng po x y). 
Definition po_div (po : prime_order)(x y : Fpe po) : Fpe po :=
    mkFpe po (P_div (order po) (val po x) (val po y)) (div_inrng po x y). 
Definition po_neg (po : prime_order)(x : Fpe po) : Fpe po :=
    mkFpe po (P_neg (order po) (val po x)) (neg_inrng po x). 
Definition po_inv (po : prime_order)(x : Fpe po) : Fpe po :=
    mkFpe po (P_inv (order po) (val po x)) (inv_inrng po x). 
Definition po_sq (po : prime_order)(x : Fpe po) : Fpe po :=
    mkFpe po (P_sq (order po) (val po x)) (sq_inrng po x). 

(* TODO Consider make pf_builder a constructor of Field *)
Definition pf_builder (p a b : N)(gt3 : p > 3) : Field :=
  let po := mkpo p gt3 in
  let U := Fpe po in
  mkField U (pfe_builder po 0) (pfe_builder po 1) 
  (po_neg po) (po_inv po) (po_add po) (po_sub po) (po_mul po)
  (po_div po) (po_sq po).
   