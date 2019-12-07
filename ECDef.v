Require Export DataTypes. 

(* Prime field element: O or coordinated point *)
Inductive GE : Set :=
  InfO : GE | Cop : N * N -> GE. 

(*TODO rename *)

Definition P_add (x y q : N) :=
  (x + y) mod q. 

Definition B_add (x y : N) : N :=
  N.lxor x y.

Definition P_mul (x y q : N) :=
  (x * y) mod q. 

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

Open Scope positive_scope. 
Fixpoint B_mul_pos (x : positive)(y : N) : N :=
  match x with
  | 1 => y
  | p~0 => N.double (B_mul_pos p y) 
  | p~1 => B_add y (N.double (B_mul_pos p y))
  end. 
Close Scope positive_scope. 

Definition B_mul (x y g : N) : N :=
  match x with
  | 0 => 0
  | Npos p => B_mod (B_mul_pos p y) g
  end.

Definition P_sub (x y q : N) :=
  (q + x - y) mod q.

Definition P_sq (x q : N) :=
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

Definition power_general (g : N)(a : N)(q : N)(sq md : N -> N -> N)
  (mp : N -> N -> N -> N)  : N :=
  let e := md a (q - 1) in
  power_tail g (N2bL e) q sq md mp 1. 

Definition P_power (g : N)(a : N)(q : N) : N :=
  power_general g a q P_sq N.modulo P_mul. 

Definition P_inv (g q : N) :=
  P_power g (q - 2) q. 
  
Definition P_div (x : N)(y : N)(q : N) : N :=
  (N.mul x (P_inv y q)) mod q. 

(* Test whether (x, y) is on the elliptic-curve defined by a b p *)
Definition OnCurve (x y p a b : N) : bool := 
  ((N.square y) mod p =? ((P_power x 3 p) + a * x + b) mod p). 

Compute OnCurve 2 4 7 1 6. 

Definition pf_eqb (P1 P2 : GE) : bool :=
  match P1, P2 with
  | InfO, InfO => true
  | InfO, _ => false
  | _, InfO => false
  | Cop (x1, y1), Cop (x2, y2) =>
      andb (x1 =? x2) (y1 =? y2)
  end.

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
(* 3.2.3.1 also A.1.2.2 *)
Definition pf_double (P1 : GE)(p : N)(a : N) :=
  match P1 with
  | InfO => InfO
  | Cop (x1, y1) =>
      let lambda := P_div (3 * (square x1) + a) (double y1) p in
      let x3 := P_sub (square lambda) ((double x1) mod p) p in
      let y3 := P_sub (lambda * (P_sub x1 x3 p)) y1 p in
        Cop (x3, y3)
  end. 
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

Definition pf_add (P1 P2 : GE)(p a : N):=
  match P1, P2 with
  | InfO, _ => P2
  | _, InfO => P1
  | Cop (x1, y1), Cop (x2, y2) =>
      match x1 =? x2, y1 + y2 =? p with
      | true, true => InfO
      | true, false => pf_double P1 p a
      | false, _ => 
        let lambda := P_div (P_sub y2  y1 p) (P_sub x2 x1 p) p in
          let x3 := ((square lambda) + 2 * p - x1 - x2) mod p in
          let y3 := P_sub (lambda * (P_sub x1 x3 p)) y1 p in
            Cop (x3, y3)
      end
  end. 

(* A.3.2 method 1*)
Fixpoint pf_mul_tail (P : GE)(kl : bL)(p : N)(a : N)(acc : GE) : GE :=
  match kl with
  | [] => acc
  | false :: tl =>
      pf_mul_tail P tl p a (pf_double acc p a)
  | true :: tl =>
      pf_mul_tail P tl p a (pf_add P (pf_double acc p a) p a)
  end. 

Definition pf_mul (P : GE)(k p a: N) : GE :=
  pf_mul_tail P (N2bL k) p a InfO. 

Fixpoint pf_mul_naive (P : GE)(k : nat)(p a : N) : GE :=
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
