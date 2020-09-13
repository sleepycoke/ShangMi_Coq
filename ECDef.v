Require Import NArith.
Require Export ECField. 
Open Scope N_scope. 
(* Elliptic Curve Group element: O or coordinated points *)
(* Affine Coordinates *)
Inductive GE (fd : ECField) : Type :=
  InfO : GE fd | Cop : (U fd) * (U fd) -> GE fd. 

(* Projective Coordinates *)
(* Decide to use Standard Projective Coordinates only*)
Inductive GE_PC (fd : ECField) : Type :=
  Tri : (U fd) * (U fd) * (U fd) -> GE_PC fd. 
Definition InfO_PC (fd : ECField) := Tri fd (id0 fd, id1 fd, id0 fd).

Section ecdef_sec.
Variable fd : ECField.
Definition u := U fd.
Definition wp : N -> u := wrapper fd.
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
Variable a b : u.

Definition grp := GE fd. 
Definition o := InfO fd. 
Definition cop := Cop fd. 
Definition gpc := GE_PC fd. 
Definition tri := Tri fd.
Definition f2 := wp 2. 
Definition f3 := wp 3. 
Definition f4 := wp 4. 
Definition f8 := wp 8. 
Set Printing Parentheses.

Notation "- x" := (op x). 
Infix "+" := ad.
Infix "-" := sb.
Infix "*" := ml. 
Infix "/" := dv.
Infix "^" := pw. 
Infix "=?" := eq.
(* Test whether (x, y) is on the elliptic-curve defined by a b p *)
(*
Definition OnCurve_pf (p a b x y : N) : bool := 
  ((N.square y) mod p =? ((P_pow p x 3) + a * x + b) mod p). 
*)


(* Regular Condition on Primal Fields *)
Definition pf_rgl_cdt (fd : ECField)(a b : U fd) : Prop :=
  let (f4, f27) := ((wrapper fd 4), (wrapper fd 27)) in
  let ad1 := mul fd f4 (pow fd a 3) in
  let ad2 := mul fd f27 (squ fd b) in
  eql fd (add fd ad1 ad2) (id0 fd) = false. 


Inductive ECurve (fd : ECField): Type :=
  | pf_curve (a b : U fd)(rgl : pf_rgl_cdt fd a b)
  | bf_curve (a b : U fd)(rgl : b <> id0 fd). 

Definition OnCurve (fd : ECField)(curve : ECurve fd) 
  (x y : U fd) : bool := 
  match squ fd, eql fd, pow fd, add fd, mul fd
   with sq, eq, ex, ad, ml =>
    match curve with 
    | pf_curve _ a b _ => 
      eq (sq y) (ad (ad (ex x 3) (ml a x)) b)
    | bf_curve _ a b _ => 
      eq (ad (sq y) (ml x y)) (ad (ad (ex x 3) (ml a (sq x))) b)
    end
  end. 

(*
Definition OnCurve_bf (ml : N -> N -> N)(sq cb : N -> N)(a b x y : N) : bool :=
  B_add (sq y) (ml x y) =? B_add (B_add (cb x) (ml a (sq x))) b. 


Definition OnCurve_bfp (gp a b x y : N) : bool :=
  OnCurve_bf (Bp_mul gp) (Bp_sq gp) (Bp_cb gp) a b x y. 
*)

Definition AC_to_PC (af_ele : grp) : GE_PC fd :=
  match af_ele with
  | InfO _ => tri (i0, i1, i0)
  | Cop _ (x, y) => tri (x, y, id1 fd)
  end.
  
Definition PC_to_AC (P: gpc) : GE fd :=
  match P with
  | Tri _ (x, y, z) => 
    if z =? i0 then o else
      cop (x / z, y / z)
    end. 
(*
Compute PC_std_to_AC 23 (Wrap_std (Tri (0, 1, 0))).
Compute PC_std_to_AC 23 (Wrap_std (Tri (7, 7, 7))).
Compute PC_std_to_AC 23 (Wrap_std (Tri (5, 5, 7))).
*)

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
    let eq := eql fd in
    let eq0 := eq (id0 fd) in
    let ml := mul fd in
    match eq0 z1, eq0 z2 with
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
    match eq0 z1, eq0 z2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, fasle =>
      (x1 * z2 =? x2 * z1) && (eq0 (y1 * z2 + y2 * z1))
    end 
  end. 



(* A.1.2.3.1 *)
(* Double for Standard Projective Cooridnates 
  over Prime Fields*)
(* z1 * z2 = 0 imples z3 = 0 *)
(* So need no for InfO case *)
Definition pf_double_pc (P : gpc) : gpc :=
  match P with Tri _ (x1, y1, z1) =>
    let lambda1 := f3  * (sq x1) + a * (sq z1) in
    let lambda2 := f2 * (y1 * z1) in
    let lambda3 := sq y1 in
    let lambda4 := lambda3 * x1 * z1 in
    let lambda5 := sq lambda2 in
    let lambda6 := (sq lambda1) - f8 * lambda4 in
    let x3 := lambda2 * lambda6 in
    let y3 := lambda1 * (f4 * lambda4 - lambda6) - f2 * lambda5 * lambda3 in
    let z3 := lambda2 * lambda5 in
      tri (x3, y3, z3)
  end. 

(* Add for Standard Projective Cooridnates *)
Definition pf_add_pc (P1 P2 : gpc) : gpc :=
  if GE_PC_invb_pf P1 P2 then tri (id0 fd, id1 fd, id1 fd) else
  if GE_PC_eqb P1 P2 then pf_double_pc P1 else
  match P1, P2 with Tri _ (x1, y1, z1), Tri _ (x2, y2, z2) =>
    match eq0 z1, eq0 z2 with
    | true, _ => P2
    | _, true => P1
    | _, _ =>
      let lambda1 := x1 * z2 in
      let lambda2 := x2 * z1 in
      let lambda3 := lambda1 - lambda2 in
      let lambda4 := y1 * z2 in
      let lambda5 := y2 * z1 in
      let lambda6 := lambda4 * lambda5 in
      let lambda7 := lambda1 * lambda2 in
      let lambda8 := z1 * z2 in
      let lambda9 := sq lambda3 in
      let lambda10 := lambda3 * lambda9 in
      let lambda11 := lambda8 * (sq lambda6) - lambda7 * lambda9 in
      let x3 := lambda3 * lambda11 in
      let y3 := lambda6 * (lambda9 * lambda1 - lambda11) - lambda4 * lambda10 in 
      let z3 := lambda10 * lambda8 in
      tri (x3, y3, z3)
    end
  end.


(* 3.2.3.1*)

Definition pf_double_ac (P : grp):=
  match P with
  | InfO _ => o
  | Cop _ (x1, y1) =>
      let lambda := (f3 * (sq x1) + a) / (f2 * y1) in
      let x3 := (sq lambda) - (f2 * x1) in
      let y3 := lambda * (x1 - x3) - y1 in
        cop (x3, y3)
  end. 

Definition pf_add_ac (P1 P2 : grp): grp :=
  match P1, P2 with
  | InfO _, _ => P2
  | _, InfO _ => P1
  | Cop _ (x1, y1), Cop _ (x2, y2) =>
      match x1 =? x2, y1 =? - y2 with
      | true, true => o 
      | true, false => pf_double_ac P1
      | false, _ => 
        let lambda := (y2 - y1) / (x2 - x1) in
          let x3 := (sq lambda) - x1 - x2 in
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
Fixpoint GE_mul_tail (A : Type)(adder dbler : A -> A)(kl : bL) (acc : A) : A :=
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

Definition GE_mul_pc (pc_to_ac : gpc -> grp)
(adder : gpc -> gpc -> gpc)
(dbler : gpc -> gpc)(P : grp)(k : N) : grp :=
  let p : gpc := AC_to_PC P in
  let r := GE_mul_tail gpc (adder p) dbler (NtobL k) (InfO_PC fd) in
  pc_to_ac r. 

(*TODO Consider merge with GE_mul_pc *)
Definition pf_mul_pc (P : grp)(k : N) : grp :=
  GE_mul_pc PC_to_AC (pf_add_pc)(pf_double_pc) P k . 

Definition pf_mul_ac (P : grp)(k : N) : grp :=
  GE_mul_ac pf_add_ac pf_double_ac P k. 

Definition pf_mul := pf_mul_pc. 
Definition pf_add := pf_add_ac. 

(*
Definition bfp_mul (m gp a : N)(P : GE)(fd : N) : GE :=
  GE_mul_ac (bfp_add m gp a) (bfp_double m gp a) P fd.   
*)

Definition GE_builder (xy : N * N) : GE fd :=
  match xy with (x, y) => Cop fd (wp x, wp y) end. 

Print Cop.
Print Tri. 

Definition GE_PC_builder (xyz : N * N * N) : GE_PC fd :=
  match xyz with (x, y, z) => Tri fd (wp x, wp y, wp z) end. 

End ecdef_sec. 

Definition GE_printer {fd : ECField}(P : GE fd) := 
  match P with 
  | InfO _ => (0, 0) 
  | Cop _ (x , y) => (unwrapper fd x, unwrapper fd y)
  end.

Definition GE_PC_printer {fd : ECField}(P : GE_PC fd) := 
  match P with 
  | Tri _ (x, y, z) => (unwrapper fd x, unwrapper fd y, unwrapper fd z)
  end.

Fact gt7 : 7 > 3. Proof. lia. Qed. 
Definition fd7 := pf_builder 7 gt7. 
Compute GE_PC_eqb fd7 (GE_PC_builder fd7 (1, 1, 2))
 (GE_PC_builder fd7 (4, 4, 1)). 
(*= true. Correct. *)

Compute GE_PC_invb_pf fd7 
 (GE_PC_builder fd7 (1, 1, 2)) (GE_PC_builder fd7 (4, 3, 1)). 
(*= true. Correct. *)

Section test.
(* Example 3 Page 12 *)
Fact gt19_3 : 19 > 3.
Proof. lia. Qed. 
Definition fd19 : ECField := pf_builder 19 gt19_3 . 
(*
Compute GE_printer (pf_double_ac fd19 (wrapper fd19 1) (GE_builder fd19 (10, 2))) .
*)
(* Correct (15, 16)*)
(*
Compute GE_printer 
(pf_add_ac fd19 (wrapper fd19 1) (GE_builder fd19 (10, 2)) (GE_builder fd19 (9, 6))) . 
*)
(* Correct (16, 3) *)
(*
Compute GE_printer (pf_mul_ac fd19 (wrapper fd19 1) (GE_builder fd19 (10, 2)) 2) .
*)
(* Correct (15, 16)*)
(*Compute GE_printer (pf_mul_pc fd19 (wrapper fd19 1) (GE_builder fd19 (10, 2)) 2) .
*)
(* Correct (15, 16)*)
(*
Compute GE_PC_printer (pf_double_pc fd19 (wrapper fd19 1)
 (GE_PC_builder fd19 (10, 2, 1))) . *)
(* Correct (10, 17, 7)*)
(*
Definition wpp := wrapper fd19. 
Compute PC_to_AC fd19 (Tri fd19 (wpp 10,wpp 17,wpp 7)).
*)(* Correct (15, 16) *) 
(* Example 6 *)
(*
Definition alpha := 2%N. 
Compute Bp_power 5 37 alpha 14. (* 29 correct *)
Compute Bp_power 5 37 alpha 31. (* 1 correct *)
Definition a6 := Bp_power 5 37 alpha 6. 
Definition a21 := Bp_power 5 37 alpha 21. 
Definition a3 := Bp_power 5 37 alpha 3. 
Definition a15 := Bp_power 5 37 alpha 15. 
Definition a24 := Bp_power 5 37 alpha 24. 
Definition a22 := Bp_power 5 37 alpha 22. 
Definition P1 := Cop (a6, a21). 
Definition P2 := Cop (a3, a15). 
Definition P3 := Cop (a24, a22). 

Compute bfp_double 5 37 1 P1 . (* 8, 31 correct *) 
Compute bfp_mul 5 37 1 P1 2 . (* 8, 31 correct *) 
Compute bfp_add 5 37 1 P1 P2 .  (* 30, 21 correct *)
*)

End test. 

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
(*
Definition p := hStoN "8542D69E 4C044F18 E8B92435 BF6FF7DE 45728391 5C45517D 722EDB8B 08F1DFC3". 
Definition a := hStoN "787968B4 FA32C3FD 2417842E 73BBFEFF 2F3C848B 6831D7E0 EC65228B 3937E498". 
Definition x2 := hStoN "64D20D27 D0632957 F8028C1E 024F6B02 EDF23102 A566C932 AE8BD613 A8E865FE".
Definition y2 := hStoN "64D20D27 D0632957 F8028C1E 024F6B02 EDF23102 A566C932 AE8BD613 A8E865FE".
Definition P2 := Cop (x2, y2). 
*)

(*
Time Compute pf_mul_ac p a P2 2. 
Time Compute pf_mul_ps p a P2 2. 
Time Compute pf_double_ps p a (AC_to_PC_std P2). 
*)
(*
Time Compute pf_mul_ac p a P2 10. (*6.397 s*)
Time Compute pf_mul_ps p a P2 10. (*3.371 s*)
Time Compute pf_mul_ac p a P2 100. (*12.66 s*)
Time Compute pf_mul_ps p a P2 100. (*3.593 s*)

Time Compute pf_mul_ac p a P2 a. (*26.911 s*)
Time Compute pf_mul_ps p a P2 a. (*617.794 s*)
*)

(*
Definition pf_double_mul (P1 : GE)(p : N)(a : N) :=
  match P1 with
  | InfO => InfO
  | Cop (x1, y1) =>
      let lambda := P_div (3 * (x1 * x1) + a) (double y1) p in
      let x3 := P_sub (lambda * lambda) ((double x1) mod p) p in
      let y3 := P_sub (lambda * (P_sub x1 x3 p)) y1 p in
        Cop (x3, y3)
  end. 
Definition pf_double_sqr (P1 : GE)(p : N)(a : N) :=
  match P1 with
  | InfO => InfO
  | Cop (x1, y1) =>
      let lambda := P_div (3 * (P_sqr x1 p) + a) (double y1) p in
      let x3 := P_sub (P_sqr lambda p) ((double x1) mod p) p in
      let y3 := P_sub (lambda * (P_sub x1 x3 p)) y1 p in
        Cop (x3, y3)
  end. 
*)

(* A.3.2 method 1*)
(*
Fixpoint pf_mul_tail (p : N)(a : N)(P : GE)(kl : bL)(acc : GE) : GE :=
  match kl with
  | [] => acc
  | false :: tl =>
      pf_mul_tail p a P tl (pf_double p a acc)
  | true :: tl =>
      pf_mul_tail p a P tl (pf_add p a P (pf_double p a acc))
  end. 

Definition pf_mul_old (p a: N)(P : GE)(fd : N) : GE :=
  pf_mul_tail p a P (NtobL fd) InfO. 
*)

(*
Fixpoint pf_mul_naive (p a : N)(P : GE)(fd : nat) : GE :=
  match fd with
  | O => InfO
  | S fd' => 
      pf_add p a P (pf_mul_naive p a P fd')
  end. 
*)

(*
(* Identical *)
Compute map (fun x => pf_mul (Cop (1, 2)) x 17 3) (Nlist 9). 
Compute map (fun x => pf_mul_old (Cop (1, 2)) x 17 3) (Nlist 9). 
Compute map (fun x => pf_mul_naive (Cop (1, 2)) (N.to_nat x) 17 3) (Nlist 9). 
*)
