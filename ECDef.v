Require Export DataTypes. 

(* Elliptic Curve Group element: O or coordinated points *)
Inductive GE : Set :=
  InfO : GE | Cop : N * N -> GE. 

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
  power_tail g (N2bL e) q sq mp 1. 

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

(* Test whether (x, y) is on the elliptic-curve defined by a b p *)
Definition OnCurve_pf (p a b x y : N) : bool := 
  ((N.square y) mod p =? ((P_power p x 3) + a * x + b) mod p). 

Definition OnCurve_bf (ml : N -> N -> N)(sq cb : N -> N)(a b x y : N) : bool :=
  B_add (sq y) (ml x y) =? B_add (B_add (cb x) (ml a (sq x))) b. 

Definition OnCurve_bfp (gp a b x y : N) : bool :=
  OnCurve_bf (Bp_mul gp) (Bp_sq gp) (Bp_cb gp) a b x y. 

Definition GE_eqb (P1 P2 : GE) : bool :=
  match P1, P2 with
  | InfO, InfO => true
  | InfO, _ => false
  | _, InfO => false
  | Cop (x1, y1), Cop (x2, y2) =>
      andb (x1 =? x2) (y1 =? y2)
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
Definition pf_double (p : N)(a : N)(P1 : GE) :=
  match P1 with
  | InfO => InfO
  | Cop (x1, y1) =>
      let lambda := P_div p (3 * (P_sq p x1) + a) (double y1) in
      let x3 := P_sub p (square lambda) ((double x1) mod p) in
      let y3 := P_sub p (lambda * (P_sub p x1 x3)) y1 in
        Cop (x3, y3)
  end. 
 
Definition pf_add (p a : N)(P1 P2 : GE) : GE :=
  match P1, P2 with
  | InfO, _ => P2
  | _, InfO => P1
  | Cop (x1, y1), Cop (x2, y2) =>
      match x1 =? x2, y1 + y2 =? p with
      | true, true => InfO
      | true, false => pf_double p a P1
      | false, _ => 
        let lambda := P_div p (P_sub p y2 y1) (P_sub p x2 x1) in
          let x3 := ((square lambda) + 2 * p - x1 - x2) mod p in
          let y3 := P_sub p (lambda * (P_sub p x1 x3)) y1 in
            Cop (x3, y3)
      end
  end. 

  
(*
Definition p := hS2N "8542D69E 4C044F18 E8B92435 BF6FF7DE 45728391 5C45517D 722EDB8B 08F1DFC3". 
Definition a := hS2N "787968B4 FA32C3FD 2417842E 73BBFEFF 2F3C848B 6831D7E0 EC65228B 3937E498". 
Definition x2 := hS2N "64D20D27 D0632957 F8028C1E 024F6B02 EDF23102 A566C932 AE8BD613 A8E865FE".
Definition y2 := hS2N "64D20D27 D0632957 F8028C1E 024F6B02 EDF23102 A566C932 AE8BD613 A8E865FE".
Definition P2 := Cop (x2, y2). 

Time Compute pf_double_sqr P2 p 2.  (* 25 68 1.9s *)
Time Compute pf_double P2 p 2. (* 1.681 secs originally *)
Time Compute pf_double_mul P2 p 2. (* 1.607 secs *)
Locate Pos.square. 
Print Pos.square. 
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
  pf_mul_tail p a P (N2bL k) InfO. 
*)


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
Fixpoint GE_mul_tail (ad db : GE -> GE)(kl : bL)(acc : GE) : GE :=
  match kl with
  | [] => acc
  | head :: tl =>
      let double := db acc in
        GE_mul_tail ad db tl 
          match head with
          | false => double
          | true => ad double
          end
  end. 

Definition GE_mul (adder : GE -> GE -> GE)(db : GE -> GE)(P : GE)(k : N) : GE :=
  GE_mul_tail (adder P) db (N2bL k) InfO.

Definition pf_mul (p a : N)(P : GE)(k : N) : GE :=
  GE_mul (pf_add p a)(pf_double p a) P k. 

Definition bfp_mul (m gp a : N)(P : GE)(k : N) : GE :=
  GE_mul (bfp_add m gp a) (bfp_double m gp a) P k.   

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
(* Example 3 *)
(*
Compute pf_double 19 1 (Cop (10, 2)) . (* Correct (15, 16)*)
Compute pf_add 19 1 (Cop (10, 2)) (Cop (9, 6)) . (* Correct (16, 3) *)
Compute pf_mul 19 1 (Cop (10, 2)) 2 . (* Correct (15, 16)*)
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
