Require Export BasicTypes. 
(* Primal field arithmetics. *)
Definition P_add (p x y : N) :=
  (x + y) mod p. 

Definition P_mul (p x y : N) :=
  (x * y) mod p.

Definition P_opp (p x : N) :=
  (p - (x mod p)) mod p. 

Definition P_sub (p x y : N) :=
  P_add p x (P_opp p y). 

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

Definition P_pow (p : N)(g : N)(a : N) : N :=
  power_general g a p (P_sq p) (P_mul p). 

(* B.1.2 *)
Definition P_inv (p g : N) :=
  P_pow p g (p - 2). 
Definition P_div (p : N)(x : N)(y : N) : N :=
  P_mul p x (P_inv p y). 

(*4.2.5*)
(*Inductive field_type : Set :=
  pri : field_type | ext : field_type .*)
(* The order of a primal field, a prime number greater than 3 *)
Record prime_order : Type := mkpo {order : N; gt3 : order > 3 }. 

(* The type of an element in F_p *)
Record Fpe (po : prime_order) : Type := 
  mkFpe {val : N; inrng : val < order po}. 
(* The type of an element in F_2m *)
Record Fbe (len : N) : Type := mkFbe {num : N; inlen : N.size num <= len}. 

(* U is the type of field elements. id0 is the identity of addition.
id1 is the identity of multiplication. wrp is wrapper from N to U and
uwp is the unwrapper. The rest are operators on the field.  *)
Class ECField (U: Type) : Type := mkField {wrp : N -> U; uwp : U -> N;
  id0 : U; id1 : U; eql : U -> U -> bool; opp : U -> U;
     inv : U -> U; add : U -> U -> U; sub : U -> U -> U;
       mul : U -> U -> U; div : U -> U -> U; dbl : U -> U;
         squ : U -> U; pow : U -> N -> U}. 
Definition wrapper {U : Type}(fd : ECField U):= @wrp _ fd. 
Definition unwrapper {U : Type}(fd : ECField U):= @uwp _ fd. 
        
Section inrng_sec. 
Context (po : prime_order). 
Lemma mod_inrng (a : N) :
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

Definition pfe_builder (n : N) : Fpe po :=
  mkFpe po (n mod (order po)) (mod_inrng n). 

Definition pfe_id0_bd : Fpe po :=
pfe_builder 0. 

Lemma add_inrng (x y : Fpe po) : 
P_add (order po) (val po x) (val po y) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma opp_inrng (x : Fpe po) : 
P_opp (order po) (val po x) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma sub_inrng (x y : Fpe po) : 
P_sub (order po) (val po x) (val po y) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma dbl_inrng (x : Fpe po) : 
(N.double  (val po x)) mod (order po) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma sq_inrng (x : Fpe po) : 
P_sq (order po) (val po x) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma pow_inrng (g : Fpe po)(a : N): 
P_pow (order po) (val po g) a < (order po). 
Proof. 
Admitted. 

Lemma mul_inrng (x y : Fpe po) : 
P_mul (order po) (val po x) (val po y) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma div_inrng (x y : Fpe po) : 
P_div (order po) (val po x) (val po y) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma inv_inrng (x : Fpe po) : 
P_inv (order po) (val po x) < (order po). 
Proof. Admitted. 

Definition po_eq (x y : Fpe po) : bool :=
(val po x) =? (val po y). 
Definition po_add (x y : Fpe po) : Fpe po :=
  mkFpe po (P_add (order po) (val po x) (val po y)) (add_inrng x y). 
Definition po_sub (x y : Fpe po) : Fpe po :=
  mkFpe po (P_sub (order po) (val po x) (val po y)) (sub_inrng x y). 
Definition po_mul (x y : Fpe po) : Fpe po :=
  mkFpe po (P_mul (order po) (val po x) (val po y)) (mul_inrng x y). 
Definition po_div (x y : Fpe po) : Fpe po :=
  mkFpe po (P_div (order po) (val po x) (val po y)) (div_inrng x y). 
Definition po_opp (x : Fpe po) : Fpe po :=
  mkFpe po (P_opp (order po) (val po x)) (opp_inrng x). 
Definition po_inv (x : Fpe po) : Fpe po :=
  mkFpe po (P_inv (order po) (val po x)) (inv_inrng x). 
Definition po_dbl (x : Fpe po) : Fpe po :=
  mkFpe po ( (N.double (val po x)) mod (order po) ) (dbl_inrng x). 
Definition po_sq (x : Fpe po) : Fpe po :=
  mkFpe po (P_sq (order po) (val po x)) (sq_inrng x). 
Definition po_pow (g : Fpe po)(a : N) : Fpe po :=
  mkFpe po (P_pow (order po) (val po g) a) (pow_inrng g a). 
End inrng_sec. 

(* TODO Consider make pf_builder a constructor of ECField *)
(* : ECField (Fpe {| order := p; gt3 := gt3 |})*)
Definition pf_builder (p : N)(gt3 : p > 3) :=
let po := mkpo p gt3 in
let U := Fpe po in
mkField U (pfe_builder po) (val po)
(pfe_builder po 0) (pfe_builder po 1) (po_eq po)
(po_opp po) (po_inv po) (po_add po) (po_sub po) (po_mul po)
  (po_div po) (po_dbl po) (po_sq po) (po_pow po).

Inductive FieldType : Type := primal_field | binary_field.  

(*
Context {fd : ECField}
Definition u := U fd.
Definition wp : N -> u := wrp fd.
Definition uw : u -> N := uwp fd.
Definition i0 := id0 fd.
Definition i1 := id1 fd.
Definition eq : u -> u -> bool := eql fd.
Definition eq0 := eq i0. 
Definition op := opp fd.
Definition iv := inv fd.
Definition ad := add fd.
Definition sb := sub fd.
Definition ml := mul fd.
Definition dv := div fd.
Definition sq := squ fd.
Definition db := dbl fd.
Definition pw := pow fd.



Notation "- x" := (op x). 
Infix "+" := ad.
Infix "-" := sb.
Infix "*" := ml. 
Infix "/" := dv.
Infix "^" := pw. 
Infix "=?" := eq.
*)
Declare Scope ecfield_scope. 
Open Scope ecfield_scope. 
Notation "- x" := (opp x) : ecfield_scope.
Infix "+" := add : ecfield_scope. 
Infix "-" := sub : ecfield_scope.
Infix "*" := mul : ecfield_scope.
Infix "/" := div : ecfield_scope.
Infix "^" := pow : ecfield_scope.
Infix "=?" := eql : ecfield_scope. 
(* Regular Condition on Primal Fields *)
Definition pf_rgl_cdt {U : Type}{_ : ECField U}(a b : U) : Prop :=
  let (f4, f27) := (wrp 4, wrp 27) in
  let ad1 := f4 * (a^3) in
  let ad2 := f27 * (squ b) in
    ad1 + ad2 =? id0 = false. 

Inductive ECurve {U : Type}{fd : ECField U} : Type :=
  | pf_curve (a b : U) (rgl : pf_rgl_cdt a b) 
  | bf_curve (a b : U) (rgl : b =? id0 = false) . 

(*
Inductive EC_Field : Type :=
  | primal : ECField -> EC_Field
  | binary : ECField -> EC_Field.
*)
(* Same as NtoBL *)
(*Definition FieldtoBL_p (fd : ECField)(ele : U fd) :=  
  NtoBL (uwr fd ele). *)
Definition FieldtoBL_p := NtoBL.


Definition FieldtoBL_b (m : N) :=
  NtoBL_len (N.to_nat (div_ceil_N m 8)). 

Definition FieldtoBL {U : Type}{fd : ECField U}(crv : ECurve)(ele : U) :=
  match crv with 
  | pf_curve _ _ _ => NtoBL (uwp ele)
  | bf_curve _ _ _ => NtoBL (uwp ele)
  end.

 Definition FieldtobL {U : Type}{fd : ECField U}(crv : ECurve)(ele : U) :=
  match crv with 
  | pf_curve _ _ _ => NtoBbL (uwp ele)
  | bf_curve _ _ _ => NtoBbL (uwp ele)
  end.

(*4.2.6*)
Definition BLtoField_p (Bl : BL)(q : N) : option N :=
  (fun (alpha : N)  => if leb q alpha then None else Some alpha) (BLtoN Bl).  

Definition BLtoField_b (Bl : BL)(m : N) : option N :=
  BLtoField_p Bl (N.shiftl 1 m). 

(*
Definition BLtoField_b (Bl : BL) : bL :=
  BLtobL Bl. 
*)

(*4.2.7*)
(* Still no need to convert since we are using N *)
(*
Definition FieldtoN_m (alpha : bL) : N :=
  bLtoN alpha. 
  *)

Close Scope list_scope.
