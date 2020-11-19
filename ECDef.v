Require Import NArith.
Require Export ECField. 

(* Elliptic Curve Group element: O or coordinated points *)
(* Affine Coordinates *)
Inductive GE {U : Type}(fd : ECField U) : Type :=
  InfO : GE fd | Cop : U * U -> GE fd. 
Check @GE. 

(* Projective Coordinates *)
(* Decide to use Standard Projective Coordinates only*)
Inductive GE_PC {U : Type}(fd : ECField U) : Type :=
  Tri : U * U * U -> GE_PC fd. 
Definition InfO_PC {U : Type}(fd : ECField U) := 
  Tri fd (id0, id1, id0).

(*Wraps an N * N to a GE*)
Definition GE_wp {U : Type}(fd : ECField U)(xy : N * N) : GE fd :=
  match xy with (x, y) => Cop fd (wrp x, wrp y) end.
    
(*Wraps an N * N * N to a GE_PC*)
Definition GE_PC_wp {U : Type}(fd : ECField U)(xyz : N * N * N) : GE_PC fd :=
  match xyz with (x, y, z) => Tri fd (wrp x, wrp y, wrp z) end.

(*Unwraps a GE to an N * N *)
Definition GE_uwp {U : Type}{fd : ECField U}(P : GE fd) := 
  match P with 
  | InfO _ => (0, 0) 
  | Cop _ (x , y) => (uwp x, uwp y)
  end.

(*Unwraps a GE_PC to an N * N * N *)
Definition GE_PC_uwp {U : Type}{fd : ECField U}(P : GE_PC fd) := 
  match P with 
  | Tri _ (x, y, z) => (uwp x, uwp y, uwp z)
  end.
(* Test whether (x, y) is on the elliptic-curve defined by a b p *)
Open Scope N_scope. 
  Definition OnCurve_pf (p a b x y : N) : bool := 
    ((N.square y) mod p =? ((P_pow p x 3) + a * x + b) mod p). 
Open Scope ecfield_scope. 

Section ecarith_sec. 
Context {U : Type}{fd : ECField U}. 
Definition grp := GE fd. 
Definition o := InfO fd. 
Definition o_pc := InfO_PC fd. 
Definition cop := Cop fd. 
Definition gpc := GE_PC fd. 
Definition tri := Tri fd.
Definition f2 := wrp 2. 
Definition f3 := wrp 3. 
Definition f4 := wrp 4. 
Definition f8 := wrp 8.

Definition OnCurve (curve : ECurve) (point : grp) : bool := 
  match point with 
  | InfO _ => true
  | Cop _ (x, y) =>
    match curve with 
    | pf_curve a b _ => 
      (squ y) =? (x^3 + a*x + b)
    (*| bf_curve a b _ => 
      (squ y) + x * y =? ((x^3) + (a*(squ x))) + b*)
    end
  end.

(*Definition OnCurve (curve : ECurve) (x y : U) : bool := 
  match curve with 
  | pf_curve a b _ => 
    (squ y) =? (x^3 + a*x + b)
  | bf_curve a b _ => 
    (squ y) + x * y =? ((x^3) + (a*(squ x))) + b
  end.*)


(*
Definition OnCurve_bf (ml : N -> N -> N)(sq cb : N -> N)(a b x y : N) : bool :=
  B_add (sq y) (ml x y) =? B_add (B_add (cb x) (ml a (sq x))) b. 


Definition OnCurve_bfp (gp a b x y : N) : bool :=
  OnCurve_bf (Bp_mul gp) (Bp_sq gp) (Bp_cb gp) a b x y. 
*)

Definition AC_to_PC (ac_ele : grp) : gpc :=
  match ac_ele with
  | InfO _ => o_pc
  | Cop _ (x, y) => tri (x, y, id1)
  end.
  
Definition PC_to_AC (pc_ele : gpc) : grp :=
  match pc_ele with
  | Tri _ (x, y, z) => 
    if z =? id0 then o else
      cop (x / z, y / z)
    end. 


Definition GE_eqb (P1 P2 : grp) : bool :=
  match P1, P2 with
  | InfO _, InfO _ => true
  | InfO _, _ => false
  | _, InfO _ => false
  | Cop _ (x1, y1), Cop _ (x2, y2) =>
      andb (x1 =? x2) (y1 =? y2)
  end.

Definition GE_PC_eqb (P1 P2 : gpc) : bool :=
  match P1, P2 with 
    Tri _ (x1, y1, z1), Tri _ (x2, y2, z2) =>
    match z1 =? id0, z2 =? id0 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false =>
      (x1 * z2 =? x2 * z1) && (y1 * z2 =? y2 * z1)
    end 
  end.

(* Whether P1 + P2 = 0 *)
Definition GE_PC_invb_pf (P1 P2 : gpc) : bool :=
  match P1, P2 with 
    Tri _ (x1, y1, z1),
    Tri _ (x2, y2, z2) =>
    match z1 =? id0, z2 =? id0 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, fasle =>
      (x1 * z2 =? x2 * z1) && (y1 * z2 + y2 * z1 =? id0)
    end 
  end. 



(* A.1.2.3.1 *)
(* Double for Standard Projective Cooridnates 
  over Prime Fields*)
(* z1 * z2 = 0 implies z3 = 0 *)
(* So need no for InfO case *)
Definition pf_double_pc (a : U)(P : gpc) : gpc :=
  match P with Tri _ (x1, y1, z1) =>
    let lambda1 := f3  * (squ x1) + a * (squ z1) in
    let lambda2 := f2 * (y1 * z1) in
    let lambda3 := squ y1 in
    let lambda4 := lambda3 * x1 * z1 in
    let lambda5 := squ lambda2 in
    let lambda6 := (squ lambda1) - f8 * lambda4 in
    let x3 := lambda2 * lambda6 in
    let y3 := lambda1 * (f4 * lambda4 - lambda6) - f2 * lambda5 * lambda3 in
    let z3 := lambda2 * lambda5 in
      tri (x3, y3, z3)
  end. 

(* Add for Standard Projective Cooridnates *)
Definition pf_add_pc (a : U)(P1 P2 : gpc) : gpc :=
  if GE_PC_invb_pf P1 P2 then tri (id0, id1, id0) else
  if GE_PC_eqb P1 P2 then pf_double_pc a P1 else
  match P1, P2 with Tri _ (x1, y1, z1), Tri _ (x2, y2, z2) =>
    match z1 =? id0, z2 =? id0 with
    | true, _ => P2
    | _, true => P1
    | _, _ =>
      let lambda1 := x1 * z2 in
      let lambda2 := x2 * z1 in
      let lambda3 := lambda1 - lambda2 in
      let lambda4 := y1 * z2 in
      let lambda5 := y2 * z1 in
      let lambda6 := lambda4 - lambda5 in
      let lambda7 := lambda1 + lambda2 in
      let lambda8 := z1 * z2 in
      let lambda9 := squ lambda3 in
      let lambda10 := lambda3 * lambda9 in
      let lambda11 := lambda8 * (squ lambda6) - lambda7 * lambda9 in
      let x3 := lambda3 * lambda11 in
      let y3 := lambda6 * (lambda9 * lambda1 - lambda11) - lambda4 * lambda10 in 
      let z3 := lambda10 * lambda8 in
      tri (x3, y3, z3)
    end
  end.


(* 3.2.3.1*)

Definition pf_double_ac (a : U)(P : grp):=
  match P with
  | InfO _ => o
  | Cop _ (x1, y1) =>
      let lambda := (f3 * (squ x1) + a) / (f2 * y1) in
      let x3 := (squ lambda) - (f2 * x1) in
      let y3 := lambda * (x1 - x3) - y1 in
        cop (x3, y3)
  end. 

Definition pf_add_ac (a : U)(P1 P2 : grp): grp :=
  match P1, P2 with
  | InfO _, _ => P2
  | _, InfO _ => P1
  | Cop _ (x1, y1), Cop _ (x2, y2) =>
      match x1 =? x2, y1 =? - y2 with
      | true, true => o 
      | true, false => pf_double_ac a P1
      | false, _ => 
        let lambda := (y2 - y1) / (x2 - x1) in
          let x3 := (squ lambda) - x1 - x2 in
          let y3 := (lambda * (x1 - x3)) - y1 in
            cop (x3, y3)
      end
  end. 

(*
(* 3.2.3.2 *)
Definition bf_double : GE fd :=
  match P1 with
  | InfO _ => o
  | Cop _ (x1, y1) =>
      let lambda := B_add x1 (y1 / x1) in
      let x3 := B_add (B_add (sq lambda) lambda) a in
      let y3 := B_add (sq x1) (B_add lambda 1) * x3 in
        cop (x3, y3)
  end. 

Definition bfp_double (m gp a : N)(P1 : GE): GE :=
  bf_double (Bp_mul gp) (Bp_div m gp) (Bp_sq gp) a P1. 


Definition bf_add (ml dv : N -> N -> N)(sq : N -> N)(a : N)(P1 P2 : GE) : GE :=
  match P1, P2 with
  | InfO, _ => P2
  | _, InfO => P1
  | Cop (x1, y1), Cop (x2, y2) =>
      match x1 =? x2, y2 =? B_add x1 y1 with
      | true, true => InfO
      | true, false => bf_double ml dv sq a P1 
      | false, _ =>
          let lambda := dv (B_add y1 y2) (B_add x1 x2) in
          let x3 := B_add (B_add (B_add (B_add (sq lambda) lambda) x1) x2) a in
          let y3 := B_add (B_add (ml lambda (B_add x1 x3)) x3) y1 in
            Cop (x3, y3)
      end
  end. 

Definition bfp_add (m gp a : N)(P1 P2 : GE) : GE :=
  bf_add (Bp_mul gp) (Bp_div m gp) (Bp_sq gp) a P1 P2. 
*)

(* A.3.2 *)
Fixpoint GE_mul_tail (A : Type)(adder dbler : A -> A)(kl : bL)
   (acc : A) : A :=
  match kl with
  | [] => acc
  | head :: tl =>
      let double := dbler acc in
        GE_mul_tail A adder dbler tl 
          match head with
          | false => double
          | true => adder double
          end
  end. 

Definition GE_mul_ac (adder : grp -> grp -> grp)(dbler : grp -> grp)
    (P : grp)(k : N) : grp :=
  GE_mul_tail grp (adder P) dbler (NtobL k) o.

Definition GE_mul_pc (adder : gpc -> gpc -> gpc)
(dbler : gpc -> gpc)(P : grp)(k : N) : grp :=
  let p : gpc := AC_to_PC P in
  let r := GE_mul_tail gpc (adder p) dbler (NtobL k) (InfO_PC fd) in
  PC_to_AC r.  

(*TODO Consider merge with GE_mul_pc *)
Definition pf_mul_pc (a : U)(P : grp)(k : N) : grp :=
  GE_mul_pc (pf_add_pc a) (pf_double_pc a) P k . 

Definition pf_mul_ac (a : U)(P : grp)(k : N) : grp :=
  GE_mul_ac (pf_add_ac a) (pf_double_ac a) P k. 

(*
Definition bfp_mul (m gp a : N)(P : GE)(fd : N) : GE :=
  GE_mul_ac (bfp_add m gp a) (bfp_double m gp a) P fd.   
*)

End ecarith_sec. 

Definition pf_mul {U : Type}{fd : ECField U} := @pf_mul_pc U fd. 
Definition pf_add {U : Type}{fd : ECField U} := @pf_add_ac U fd. 

Definition ml_ad_extractor {U : Type}{fd : ECField U}(curve : ECurve) := 
  match curve with
  | pf_curve a _ _ => (pf_mul a, pf_add a)
  (*| bf_curve a _ _ => (pf_mul a, pf_add a)*)
  end. (*TODO bf case*)


(*
Definition decode_TPB (code : N * N) : N :=
  match code with
  | (m, fd)  =>
      (N.shiftl 1 m) + (N.shiftl 1 fd) + 1
  end. 

Definition decode_PPB (code : N * (N * N * N)) : N :=
  match code with
  | (m, (k1, k2, k3)) =>
      (N.shiftl 1 m) + (N.shiftl 1 k1) + (N.shiftl 1 k2) + (N.shiftl 1 k3) + 1
  end. 
*)