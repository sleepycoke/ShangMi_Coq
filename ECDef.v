Require Export Field. 


(* Test whether (x, y) is on the elliptic-curve defined by a b p *)
Definition OnCurve_pf (p a b x y : N) : bool := 
  ((N.square y) mod p =? ((P_power p x 3) + a * x + b) mod p). 

Definition OnCurve_bf (ml : N -> N -> N)(sq cb : N -> N)(a b x y : N) : bool :=
  B_add (sq y) (ml x y) =? B_add (B_add (cb x) (ml a (sq x))) b. 

Definition OnCurve_bfp (gp a b x y : N) : bool :=
  OnCurve_bf (Bp_mul gp) (Bp_sq gp) (Bp_cb gp) a b x y. 

(* Elliptic Curve Group element: O or coordinated points *)
(* Affine Coordinates *)
Inductive GE : Set :=
  InfO : GE | Cop : N * N -> GE. 

(* Projective Coordinates *)
Inductive GE_PC : Set :=
  Tri : N * N * N -> GE_PC. 
Definition InfO_PC := Tri (0, 1, 0).
(* Standard Projective Coordinates *)
Inductive GE_PC_std : Set :=
  Wrap_std : GE_PC -> GE_PC_std. 
Definition InfO_ps := Wrap_std InfO_PC. 

Definition Tri_ps (t : N * N * N) :=
  Wrap_std (Tri t). 

(* Jacobian Projective Coordinates *)
Inductive GE_PC_jac : Set :=
  Wrap_jac : GE_PC -> GE_PC_jac. 
Definition Tri_pj (t : N * N * N) :=
  Wrap_jac (Tri t). 
Definition InfO_pj := Wrap_jac InfO_PC. 

Definition AC_to_PC (af_ele : GE) : GE_PC :=
  match af_ele with
  | InfO => Tri (0, 1, 0)
  | Cop (x, y) => Tri (x, y, 1)
  end. 

Definition AC_to_PC_std (af_ele : GE) : GE_PC_std :=
  Wrap_std (AC_to_PC af_ele). 

Definition ACtoPC_jac (af_ele : GE) : GE_PC_jac :=
  Wrap_jac (AC_to_PC af_ele). 

Definition PC_std_to_AC (p : N)(std_ele : GE_PC_std) : GE :=
  match std_ele with
  | Wrap_std (Tri (_, _, 0)) => InfO
  | Wrap_std (Tri (x, y, z)) => 
    Cop (P_div p x z, P_div p y z)
    end. 

(*
Compute PC_std_to_AC 23 (Wrap_std (Tri (0, 1, 0))).
Compute PC_std_to_AC 23 (Wrap_std (Tri (7, 7, 7))).
Compute PC_std_to_AC 23 (Wrap_std (Tri (5, 5, 7))).
*)

Definition GE_eqb (P1 P2 : GE) : bool :=
  match P1, P2 with
  | InfO, InfO => true
  | InfO, _ => false
  | _, InfO => false
  | Cop (x1, y1), Cop (x2, y2) =>
      andb (x1 =? x2) (y1 =? y2)
  end.

Definition GE_PC_std_eqb (p : N)(P1 P2 : GE_PC_std) : bool :=
  match P1, P2 with 
    Wrap_std (Tri (x1, y1, z1)),
    Wrap_std (Tri (x2, y2, z2)) =>
    match z1, z2 with
    | 0, 0 => true
    | 0, _ => false
    | _, 0 => false
    | _, _ =>
      andb ((x1 * z2) mod p =? (x2 * z1) mod p)
        ((y1 * z2) mod p =? (y2 * z1) mod p)
    end 
  end. 

Definition GE_PC_std_invb_pf (p : N)(P1 P2 : GE_PC_std) : bool :=
  match P1, P2 with 
    Wrap_std (Tri (x1, y1, z1)),
    Wrap_std (Tri (x2, y2, z2)) =>
    match z1, z2 with
    | 0, 0 => true
    | 0, _ => false
    | _, 0 => false
    | _, _ =>
      andb ((x1 * z2) mod p =? (x2 * z1) mod p)
        ((y1 * z2 + y2 * z1) mod p =? 0)
    end 
  end. 

(* TODO *)
(*
  Definition GE_PC_std_invb_bf (p : N)(P1 P2 : GE_PC_std) : bool :=
  match P1, P2 with 
    Wrap_std (Tri (x1, y1, z1)),
    Wrap_std (Tri (x2, y2, z2)) =>
    match z1, z2 with
    | 0, 0 => true
    | 0, _ => false
    | _, 0 => false
    | _, _ =>
      andb ((x1 * z2) mod p =? (x2 * z1) mod p)
        ((y1 * z2 + y2 * z1) mod p =? 0)
    end 
  end. 
*)
(* 
Compute GE_PC_std_eqb 7 
  (Wrap_std (Tri (1, 1, 2)))
  (Wrap_std (Tri (4, 4, 1))). 
= true. Correct. 

Compute GE_PC_std_inv 7
  (Wrap_std (Tri (1, 1, 2)))
  (Wrap_std (Tri (4, 3, 1))). 
= true. Correct. *)

(* A.1.2.3.1 *)
(* Double for Standard Projective Cooridnates 
  over Prime Fields*)
(* z1 * z2 = 0 imples z3 = 0 *)
(* So need no for InfO case *)
Definition pf_double_ps (p a : N)(P : GE_PC_std) : GE_PC_std :=
  match P with (Wrap_std (Tri (x1, y1, z1))) =>
  let lambda1 := (3 * (N.square x1) + a * (N.square z1)) mod p in
  let lambda2 := (2 * y1 * z1) mod p in
  let lambda3 := (N.square y1) mod p in
  let lambda4 := (lambda3 * x1 * z1) mod p in
  let lambda5 := (N.square lambda2) mod p in
  let lambda6 := P_sub p (P_sq p lambda1)  ((8 * lambda4) mod p) in
  let x3 := (lambda2 * lambda6) mod p in
  let y3 := P_sub (lambda1 * (P_sub p (4 * lambda4) lambda6)) 
    (2 * lambda5 * lambda3)  in
  let y3 := (lambda1 * (4 * lambda4 + p - lambda6) + p -
    ((2 * lambda5 * lambda3) mod p)) mod p in
  let z3 := (lambda2 * lambda5) mod p in
    Tri_ps (x3, y3, z3)
  end. 

(* Add for Standard Projective Cooridnates *)
Definition pf_add_ps (p a : N)(P1 P2 : GE_PC_std) : GE_PC_std :=
  if GE_PC_std_invb_pf p P1 P2 then Wrap_std (Tri (0, 1, 1)) else
  if GE_PC_std_eqb p P1 P2 then pf_double_ps p a P1 else
  match P1, P2 with 
    Wrap_std (Tri (x1, y1, z1)), Wrap_std (Tri (x2, y2, z2)) =>
    match z1, z2 with
    | 0, _ => P2
    | _, 0 => P1
    | _, _ =>
      let ad := P_add p in
      let sb := P_sub p in
      let ml := P_mul p in
      let sq := P_sq p in
      let lambda1 := ml x1 z2 in
      let lambda2 := ml x2 z1 in
      let lambda3 := sb lambda1 lambda2 in
      let lambda4 := ml y1 z2 in
      let lambda5 := ml y2 z1 in
      let lambda6 := sb lambda4 lambda5 in
      let lambda7 := ad lambda1 lambda2 in
      let lambda8 := ml z1 z2 in
      let lambda9 := sq lambda3 in
      let lambda10 := ml lambda3 lambda9 in
      let lambda11 := sb (ml lambda8 (sq lambda6))
        (ml lambda7 lambda9) in
      let x3 := ml lambda3 lambda11 in
      let y3 := sb (ml lambda6 (sb (ml lambda9 lambda1) lambda11))
        (ml lambda4 lambda10) in 
      let z3 := ml lambda10 lambda8 in
      Tri_ps (x3, y3, z3)
    end
  end.



(* What is this function? *)
(*
Open Scope positive_scope. 
Fixpoint P_sqr_pos (n q : positive) : N :=
  match n with
  | 1 => 1
  | p~1 => 
      match ((P_sqr_pos p q) + (Npos p)) mod (Npos q) with
      | N0 => 1
      | Npos m => (Npos m~0~1) mod (Npos q)
      end
  | p~0 => 
      match (P_sqr_pos p q) with
      | N0 => 0
      | Npos m => (Npos m~0) mod (Npos q)
      end
  end. 
Close Scope positive_scope. 
 
Definition P_sqr (n q : N) :=
  match q with
  | 0 => n 
  | Npos q' => 
    match n with
    | 0 => 0
    | Npos n' =>
        P_sqr_pos n' q'
    end
  end. 

Compute P_sqr 4 13. 
*)

(* 3.2.3.1*)
Definition pf_double_ac (p : N)(a : N)(P1 : GE) :=
  match P1 with
  | InfO => InfO
  | Cop (x1, y1) =>
      let lambda := P_div p (3 * (P_sq p x1) + a) (double y1) in
      let x3 := P_sub p (square lambda) ((double x1) mod p) in
      let y3 := P_sub p (lambda * (P_sub p x1 x3)) y1 in
        Cop (x3, y3)
  end. 
 
Definition pf_add_ac (p a : N)(P1 P2 : GE) : GE :=
  match P1, P2 with
  | InfO, _ => P2
  | _, InfO => P1
  | Cop (x1, y1), Cop (x2, y2) =>
      match x1 =? x2, y1 + y2 =? p with
      | true, true => InfO
      | true, false => pf_double_ac p a P1
      | false, _ => 
        let lambda := P_div p (P_sub p y2 y1) (P_sub p x2 x1) in
          let x3 := ((square lambda) + 2 * p - x1 - x2) mod p in
          let y3 := P_sub p (lambda * (P_sub p x1 x3)) y1 in
            Cop (x3, y3)
      end
  end. 

  

(* 3.2.3.2 *)
Definition bf_double (ml dv : N -> N -> N)(sq : N -> N)
  (a : N)(P1 : GE): GE :=
  match P1 with
  | InfO => InfO
  | Cop (x1, y1) =>
      let lambda := B_add x1 (dv y1 x1) in
      let x3 := B_add (B_add (sq lambda) lambda) a in
      let y3 := B_add (sq x1) (ml (B_add lambda 1) x3) in
        Cop (x3, y3)
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


(* A.3.2 *)
Fixpoint GE_mul_tail (A : Type)(ad db : A -> A)(kl : bL)
  (acc : A) : A :=
  match kl with
  | [] => acc
  | head :: tl =>
      let double := db acc in
        GE_mul_tail A ad db tl 
          match head with
          | false => double
          | true => ad double
          end
  end. 

Definition GE_mul_ac (adder : GE -> GE -> GE)(db : GE -> GE)
  (P : GE)(k : N) : GE :=
  GE_mul_tail GE (adder P) db (NtobL k) InfO.

Definition GE_mul_ps (pstoac : GE_PC_std -> GE)
(adder : GE_PC_std -> GE_PC_std -> GE_PC_std)
(db : GE_PC_std -> GE_PC_std)(P : GE)(k : N) : GE :=
  let p : GE_PC_std := AC_to_PC_std P in
  let r := GE_mul_tail GE_PC_std (adder p) db (NtobL k) InfO_ps in
  pstoac r. 

Definition pf_mul_ps (p a : N)(P : GE)(k : N) : GE :=
  GE_mul_ps (PC_std_to_AC p)(pf_add_ps p a)(pf_double_ps p a) P k . 

Definition pf_mul_ac (p a : N)(P : GE)(k : N) : GE :=
  GE_mul_ac (pf_add_ac p a)(pf_double_ac p a) P k. 

Definition pf_mul := pf_mul_ps. 
Definition pf_add := pf_add_ac. 

Definition bfp_mul (m gp a : N)(P : GE)(k : N) : GE :=
  GE_mul_ac (bfp_add m gp a) (bfp_double m gp a) P k.   


(* Example 3 *)
(*
Compute pf_double_ac 19 1 (Cop (10, 2)) . (* Correct (15, 16)*)
Compute pf_add_ac 19 1 (Cop (10, 2)) (Cop (9, 6)) . (* Correct (16, 3) *)
Compute pf_mul_ac 19 1 (Cop (10, 2)) 2 . (* Correct (15, 16)*)
Compute pf_mul_ps 19 1 (Cop (10, 2)) 2 . (* Correct (15, 16)*)
Compute AC_to_PC_std (Cop(10, 2)). 
Compute pf_double_ps 19 1 (Tri_ps (10, 2, 1)) . 
(* Incorrect (10, 17, 7)*)
Compute PC_std_to_AC 19 (Tri_ps (10, 17, 7)).
(* Incorrect (15, 16) *) 
*)
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













Definition decode_TPB (code : N * N) : N :=
  match code with
  | (m, k)  =>
      (N.shiftl 1 m) + (N.shiftl 1 k) + 1
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

Definition pf_mul_old (p a: N)(P : GE)(k : N) : GE :=
  pf_mul_tail p a P (NtobL k) InfO. 
*)

(*
Fixpoint pf_mul_naive (p a : N)(P : GE)(k : nat) : GE :=
  match k with
  | O => InfO
  | S k' => 
      pf_add p a P (pf_mul_naive p a P k')
  end. 
*)

(*
(* Identical *)
Compute map (fun x => pf_mul (Cop (1, 2)) x 17 3) (Nlist 9). 
Compute map (fun x => pf_mul_old (Cop (1, 2)) x 17 3) (Nlist 9). 
Compute map (fun x => pf_mul_naive (Cop (1, 2)) (N.to_nat x) 17 3) (Nlist 9). 
*)