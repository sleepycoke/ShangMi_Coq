Require Export SMlib.
Require Export Coq.Strings.Ascii.

(* ByteList is indeed a list of bytes*)
Definition BL := list byte. 
(* BitList is indeed a list of bool*)
Definition bL := list bool. 
Fixpoint bStobL_tail (bs : string)(acc : bL) : bL :=
  match bs with
  | EmptyString => acc 
  | String head tl =>
      match ascii_to_digit head with
      | Some 1 => bStobL_tail tl (List.app acc [true])
      | _ => bStobL_tail tl (List.app acc [false])
      end
  end.

Open Scope list_scope. 

Definition bStobL (bs : string) : bL :=
  bStobL_tail bs []. 

Fixpoint bLtobS_tail (bl : bL)(acc : string) : string :=
  match bl with
  | [] => acc
  | head :: tl =>
      match head with
      | true => bLtobS_tail tl (acc ++ "1")
      | false => bLtobS_tail tl (acc ++ "0")
      end
  end.

Definition bLtobS (bl : bL) : string :=
  bLtobS_tail bl "". 

Fixpoint BLtoN_tail (Bl : BL)(acc : N) : N :=
  match Bl with
  | [] => acc
  | h :: tl =>
      BLtoN_tail tl (acc * 256 + (Byte.to_N h)) 
  end.

(*4.2.2*)
Definition BLtoN (Bl : BL) : N :=
  BLtoN_tail Bl 0.

Definition NtoByte (n : N) : byte :=
  match Byte.of_N n with
  | None => x00
  | Some b => b
  end.

Fixpoint NtoBL_tail (k : nat)(x : N)(acc : BL) : BL :=
  match k with
  | O => acc
  | S k' => 
      NtoBL_tail k' (N.div x 256) (NtoByte (N.modulo x 256) :: acc)
  end.

(*4.2.1 trunk from right*)
Definition NtoBL_len (k : nat)(x : N) : BL :=
  NtoBL_tail k x [].

Definition NtoBL (x : N) : BL :=
  NtoBL_len (N.to_nat (N.div (N.add (N.size x) 7) 8)) x. 

(* Transform the first k(<= 8) bits into an N *)  
Fixpoint bLtoN_tail (bl : bL)(k : nat)(acc : N) : N :=
  match k with
  | O => acc
  | S k' => 
      match bl with
      | [] => acc
      | h :: tl => 
          match h with
          | false => bLtoN_tail tl k' (N.double acc)
          | true => bLtoN_tail tl k' (N.add 1 (N.double acc))
          end
      end
  end.

(*4.2.2*)
Definition bLtoN (bl : bL) :=
  bLtoN_tail bl (List.length bl) 0.

Definition bLtoN_prefix (bl :bL)(k : nat) : N :=
  bLtoN_tail bl k 0.

(* tranfrom the first k bits into a byte *)
Definition bLtoByte (bl : bL)(k : nat) :=
  NtoByte (bLtoN_prefix bl k). 



(*4.2.3*)
Fixpoint bLtoBL_tail (s : bL)(k : nat)(acc : BL) : BL :=
  match k with
  | O => acc 
  | S k' =>
      (fun sl => bLtoBL_tail (fst sl) k' 
      (List.app [bLtoByte (snd sl) 8] acc)) (partListBack s 8)
  end.


Definition bLtoBL (s : bL) : BL :=
  bLtoBL_tail s (Nat.div (Nat.add(List.length s) 7%nat) 8%nat) []. 

Fixpoint NtobL_tail (n : N)(k : nat)(acc : bL) : bL :=
  match k with
  | O => acc
  | S k' => 
      NtobL_tail (N.div n 2) k' (N.odd n :: acc)
  end.

(* [] for 0, trunk from right. *)
Definition NtobL_len (len : nat)(n : N) : bL :=
  NtobL_tail n len []. 

Definition NtobL (n : N) : bL :=
  NtobL_len (N.to_nat (N.size n)) n.

Definition bStoN (bs : string) : N :=
  bLtoN (bStobL bs). 


(*4.2.4*)
(*2019-10-09, realized that I need to keep preceding 0s 
* And it is only used in KeyEx.v yet. *)
Fixpoint BLtobL_tail (M : BL)(k : nat)(acc : bL) : bL :=
  match k with
  | O => acc
  | S k'=> 
      match M with
      | [] => acc
      | h :: tl =>
          BLtobL_tail tl k' (List.app acc (NtobL_len 8 (Byte.to_N h)))
      end
  end.

Definition BLtobL (M : BL) : bL :=
  BLtobL_tail M (List.length M) [].

Definition NtoBbL (n : N) : bL := BLtobL (NtoBL n). 

(*Padding len to a multiplier of 8*)
(*Croping from the rightside *)
Definition NtoBbL_len (len : nat)(n : N) : bL := 
  BLtobL (NtoBL_len (div_ceil_nat len 8%nat) n). 

Definition NtobS (n : N) : string :=
  bLtobS (NtobL n).

Definition NtobS_len (n : N)(len : nat) : string :=
  bLtobS (NtobL_len len n).

Definition rmsp (s : string) := (RepChar s " "%char ""%string). 
Fixpoint hStobS_tail (m_hex : string)(acc : string) : string :=
  match m_hex with
  | "" => acc
  | String h tl =>
      match HexString.ascii_to_digit h with
      | None => ""
      | Some v => hStobS_tail tl (acc ++ NtobS_len v 4)
      end
  end. 

Definition hStobS (m_hex : string) : string :=
  hStobS_tail (rmsp m_hex) "".

Definition hStoN (m_hex : string) : N :=
  HexString.Raw.to_N (rmsp m_hex) 0. 

(*
Definition hChartobL (m_hex : string) : bL :=
  let rawbl := NtobL (hStoN m_hex) in
    List.app
    match (Nat.modulo (List.length rawbl) 4) with
    | 1%nat => [false; false; false] 
    | 2%nat => [false; false] 
    | 3%nat => [false]
    | _ => [false; false; false; false]
    end
    rawbl. 
    *)
Definition hStobL (hs : string) :=
  bStobL (hStobS hs). 

Definition NtohS (n : N) : string :=
  match n with
  | Npos p => HexString.Raw.of_pos p ""
  | N0 => ""
  end.  

Definition NtohChar (n : N) : string :=
  match n with
  | Npos p => HexString.Raw.of_pos p ""
  | N0 => "0"
  end. 

Fixpoint bLtohS_tail (bl : bL)(hSLen : nat)(acc : string) : string :=
  match hSLen with
  | O => acc
  | S len' =>
  let (pre, suf) := partListBack bl 4 in
    match suf with
    | [] => acc
    | _ => bLtohS_tail pre len' ((NtohChar (bLtoN suf)) ++ acc)
    end
  end.

Definition bLtohS (bl : bL) : string :=
  bLtohS_tail bl (Nat.div (Nat.add (length bl) 3%nat) 4%nat) "".

Definition bStohS (m_bin : string) : string :=
  bLtohS (bStobL m_bin). 

Fixpoint strtobL_tail (s : string)(acc : bL) :=
  match s with
  | "" => acc
  | String c tl =>
      strtobL_tail tl (List.app acc (NtobL_len 8 (N_of_ascii c)))
  end. 

Definition strtobL (s : string) :=
  strtobL_tail s [].

Fixpoint BLtostr_tail (Bl : BL)(acc : string) :=
  match Bl with
  | [] => acc
  | h :: tl =>
      BLtostr_tail tl (acc ++ (String (ascii_of_N (Byte.to_N h)) ""))
  end. 
 
Definition BLtostr (Bl : BL) :=
  BLtostr_tail Bl "". 

Definition bLtostr (bl : bL) := 
  BLtostr (bLtoBL bl). 


Fixpoint bLeqb (bl1 bl2 : bL) : bool :=
  match bl1, bl2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => 
      if Bool.eqb h1 h2 then bLeqb t1 t2
        else false
  | _, _ => false
  end. 

Fixpoint All0bL (bl : bL) : bool :=
  match bl with
  | [] => true
  | true :: tl => false
  | false :: tl =>
      All0bL tl
  end. 

Fixpoint bLXOR_tail (a b acc : bL) : bL :=
  match a, b with
  | ha :: ta, hb :: tb =>
       bLXOR_tail ta tb ((xorb ha hb) :: acc)
  | [], _ => List.app (rev b) acc
  | _, [] => List.app (rev a) acc 
  end. 

(* a and b are aligned to the right and 
 keep the overhead to the left of the result *)
Definition bLXOR (a b : bL) :=
  (bLXOR_tail (rev a) (rev b) []).

(*
Compute bLXOR (bStobL "111") (bStobL "1"). 
Compute bLXOR (bStobL "110") (bStobL "1"). 
Compute bLXOR (bStobL "011") (bStobL "1"). 
Compute bLXOR (bStobL "11111101") (bStobL "111"). 
Compute bLXOR (bStobL "111") (bStobL "11111101"). 
Compute bLXOR (bStobL "111001") (bStobL "11111101"). 
*)
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

(* The type of an element of F_p *)
Record Fpe (po : prime_order) : Type := 
  mkFpe {val : N; inrng : val < order po}. 
(* The type of an element of F_2m *)
Record Fbe (len : N) : Type := mkFbe {num : N; inlen : N.size num <= len}. 
(* U is the type of elements *)

(* U is the type of field elements. id0 is the identity of addition.
id1 is the identity of multiplication. The rest are operators on the field.  *)
Record ECField : Type := mkField {U : Type; wrp : N -> U; uwp : U -> N;
  id0 : U; id1 : U; eql : U -> U -> bool; opp : U -> U;
     inv : U -> U; add : U -> U -> U; sub : U -> U -> U;
       mul : U -> U -> U; div : U -> U -> U; dbl : U -> U;
         squ : U -> U; pow : U -> N -> U}. 

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

Lemma opp_inrng (po : prime_order)(x : Fpe po) : 
P_opp (order po) (val po x) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma sub_inrng (po : prime_order)(x y : Fpe po) : 
P_sub (order po) (val po x) (val po y) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma dbl_inrng (po : prime_order)(x : Fpe po) : 
(N.double  (val po x)) mod (order po) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma sq_inrng (po : prime_order)(x : Fpe po) : 
P_sq (order po) (val po x) < (order po). 
Proof. apply mod_inrng. Qed.

Lemma pow_inrng (po : prime_order)(g : Fpe po)(a : N): 
P_pow (order po) (val po g) a < (order po). 
Proof. 
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

Definition po_eq (po : prime_order)(x y : Fpe po) : bool :=
(val po x) =? (val po y). 
Definition po_add (po : prime_order)(x y : Fpe po) : Fpe po :=
  mkFpe po (P_add (order po) (val po x) (val po y)) (add_inrng po x y). 
Definition po_sub (po : prime_order)(x y : Fpe po) : Fpe po :=
  mkFpe po (P_sub (order po) (val po x) (val po y)) (sub_inrng po x y). 
Definition po_mul (po : prime_order)(x y : Fpe po) : Fpe po :=
  mkFpe po (P_mul (order po) (val po x) (val po y)) (mul_inrng po x y). 
Definition po_div (po : prime_order)(x y : Fpe po) : Fpe po :=
  mkFpe po (P_div (order po) (val po x) (val po y)) (div_inrng po x y). 
Definition po_opp (po : prime_order)(x : Fpe po) : Fpe po :=
  mkFpe po (P_opp (order po) (val po x)) (opp_inrng po x). 
Definition po_inv (po : prime_order)(x : Fpe po) : Fpe po :=
  mkFpe po (P_inv (order po) (val po x)) (inv_inrng po x). 
Definition po_dbl (po : prime_order)(x : Fpe po) : Fpe po :=
  mkFpe po ( (N.double (val po x)) mod (order po) ) (dbl_inrng po x). 
Definition po_sq (po : prime_order)(x : Fpe po) : Fpe po :=
  mkFpe po (P_sq (order po) (val po x)) (sq_inrng po x). 
Definition po_pow (po : prime_order)(g : Fpe po)(a : N) : Fpe po :=
  mkFpe po (P_pow (order po) (val po g) a) (pow_inrng po g a). 

(* TODO Consider make pf_builder a constructor of ECField *)
Definition pf_builder (p : N)(gt3 : p > 3) : ECField :=
let po := mkpo p gt3 in
let U := Fpe po in
mkField U (pfe_builder po) (val po)
(pfe_builder po 0) (pfe_builder po 1) (po_eq po)
(po_opp po) (po_inv po) (po_add po) (po_sub po) (po_mul po)
  (po_div po) (po_dbl po) (po_sq po) (po_pow po).
      
Inductive FieldType : Type := primal_field | binary_field.  

Module ecarith_mod.

Context {fd : ECField}. 
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

(* Regular Condition on Primal Fields *)
Definition pf_rgl_cdt (a b : u) : Prop :=
  let (f4, f27) := (wp 4, wp 27) in
  let ad1 := f4 * a^3 in
  let ad2 := f27 * (sq b) in
    ad1 + ad2 =? i0 = false. 

Inductive ECurve : Type :=
  | pf_curve (a b : u) (rgl : pf_rgl_cdt a b) 
  | bf_curve (a b : u) (rgl : b =? i0 = false) . 

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

Definition FieldtoBL (crv : ECurve)(ele : u) :=
  match crv with 
  | pf_curve _ _ _ => NtoBL (uw ele)
  | bf_curve _ _ _ => NtoBL (uw ele)
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

End ecarith_mod.