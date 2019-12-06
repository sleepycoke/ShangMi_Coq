Require Export DataTypes. 

(* Prime field element: O or coordinated point *)
Inductive FEp : Set :=
  InfO : FEp | Cop : N * N -> FEp. 

(*TODO rename *)

Definition F_add (x y q : N) :=
  (x + y) mod q. 

Definition F_mul (x y q : N) :=
  (x * y) mod q. 

Definition F_sub (x y q : N) :=
  (q + x - y) mod q.

Definition F_sq (x q : N) :=
  (N.square x) mod q. 

(*B.1.1*)
Fixpoint power_tail (g : N)(e : bL)(q : N)(sq md : N -> N -> N)
  (mp : N -> N -> N -> N)(acc : N) : N :=
  match e with
  | [] => acc
  | h :: tl =>
      power_tail g tl q sq md mp
      match h with
      | true => (mp (sq acc q) g q) 
      | false => (sq acc q)
      end
  end.

Definition power' (g : N)(a : N)(q : N)(sq md : N -> N -> N)
  (mp : N -> N -> N -> N)  : N :=
  let e := md a (q - 1) in
  power_tail g (N2bL e) q sq md mp 1. 

Definition power (g : N)(a : N)(q : N) : N :=
  power' g a q F_sq N.modulo F_mul. 

Definition inv_p (g : N)(q : N) : N :=
  power g (q - 2) q. 

Definition F_inv (g q : N) :=
  inv_p g q. 
  
Definition F_div (x : N)(y : N)(q : N) : N :=
  (N.mul x (inv_p y q)) mod q. 

(* Test whether (x, y) is on the elliptic-curve defined by a b p *)
Definition OnCurve (x y p a b : N) : bool := 
  ((N.square y) mod p =? ((power x 3 p) + a * x + b) mod p). 

Compute OnCurve 2 4 7 1 6. 

Definition pf_eqb (P1 P2 : FEp) : bool :=
  match P1, P2 with
  | InfO, InfO => true
  | InfO, _ => false
  | _, InfO => false
  | Cop (x1, y1), Cop (x2, y2) =>
      andb (x1 =? x2) (y1 =? y2)
  end.

Open Scope positive_scope. 
Fixpoint F_sqr_pos (n q : positive) : N :=
  match n with
  | 1 => 1
  | p~1 => 
      match ((F_sqr_pos p q) + (Npos p)) mod (Npos q) with
      | N0 => 1
      | Npos m => (Npos m~0~1) mod (Npos q)
      end
  | p~0 => 
      match (F_sqr_pos p q) with
      | N0 => 0
      | Npos m => (Npos m~0) mod (Npos q)
      end
  end. 
Close Scope positive_scope. 
 
Definition F_sqr (n q : N) :=
  match q with
  | 0 => n 
  | Npos q' => 
    match n with
    | 0 => 0
    | Npos n' =>
        F_sqr_pos n' q'
    end
  end. 
(* 3.2.3.1 also A.1.2.2 *)
Definition pf_double (P1 : FEp)(p : N)(a : N) :=
  match P1 with
  | InfO => InfO
  | Cop (x1, y1) =>
      let lambda := F_div (3 * (square x1) + a) (double y1) p in
      let x3 := F_sub (square lambda) ((double x1) mod p) p in
      let y3 := F_sub (lambda * (F_sub x1 x3 p)) y1 p in
        Cop (x3, y3)
  end. 
Definition pf_double_mul (P1 : FEp)(p : N)(a : N) :=
  match P1 with
  | InfO => InfO
  | Cop (x1, y1) =>
      let lambda := F_div (3 * (x1 * x1) + a) (double y1) p in
      let x3 := F_sub (lambda * lambda) ((double x1) mod p) p in
      let y3 := F_sub (lambda * (F_sub x1 x3 p)) y1 p in
        Cop (x3, y3)
  end. 
Definition pf_double_sqr (P1 : FEp)(p : N)(a : N) :=
  match P1 with
  | InfO => InfO
  | Cop (x1, y1) =>
      let lambda := F_div (3 * (F_sqr x1 p) + a) (double y1) p in
      let x3 := F_sub (F_sqr lambda p) ((double x1) mod p) p in
      let y3 := F_sub (lambda * (F_sub x1 x3 p)) y1 p in
        Cop (x3, y3)
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

Definition pf_add (P1 P2 : FEp)(p a : N):=
  match P1, P2 with
  | InfO, _ => P2
  | _, InfO => P1
  | Cop (x1, y1), Cop (x2, y2) =>
      match x1 =? x2, y1 + y2 =? p with
      | true, true => InfO
      | true, false => pf_double P1 p a
      | false, _ => 
        let lambda := F_div (F_sub y2  y1 p) (F_sub x2 x1 p) p in
          let x3 := ((square lambda) + 2 * p - x1 - x2) mod p in
          let y3 := F_sub (lambda * (F_sub x1 x3 p)) y1 p in
            Cop (x3, y3)
      end
  end. 

(* A.3.2 method 1*)
Fixpoint pf_mul_tail (P : FEp)(kl : bL)(p : N)(a : N)(acc : FEp) : FEp :=
  match kl with
  | [] => acc
  | false :: tl =>
      pf_mul_tail P tl p a (pf_double acc p a)
  | true :: tl =>
      pf_mul_tail P tl p a (pf_add P (pf_double acc p a) p a)
  end. 

Definition pf_mul (P : FEp)(k p a: N) : FEp :=
  pf_mul_tail P (N2bL k) p a InfO. 

Fixpoint pf_mul_naive (P : FEp)(k : nat)(p a : N) : FEp :=
  match k with
  | O => InfO
  | S k' => 
      pf_add P (pf_mul_naive P k' p a) p a
  end. 

(*
(* Identical *)
Compute map (fun x => pf_mul (Cop (1, 2)) x 17 3) (Nlist 9). 
Compute map (fun x => pf_mul_naive (Cop (1, 2)) (N.to_nat x) 17 3) (Nlist 9). 

(* Example 3 *)
Compute pf_add (Cop (10, 2)) (Cop (9, 6)) 19 1. (* Correct *)
Compute pf_mul (Cop (10, 2)) 2 19 1. (* Correct *)

Compute negb (3 =? 2). 
*)
