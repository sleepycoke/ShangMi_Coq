Require Export ECalg. 
Require Export SM3. 

(* TODO RANDOMLY sample a number in [low, high] *)
Definition SampleN (low : N)(high : N)(seed : N) : N :=
  low + (seed mod (high + 1 - low)). 

Compute map (SampleN 10 20) (Nlist 15). 

(* false if composite *)
Fixpoint TryFunb (l : list N)(func : N -> (bool * N)) : (bool * N * N) :=
  match l with
  | [] => (true, 0, 0)
  | j :: tl =>
      match func j with
      | (false, i) => (false, j, i) (* b.5 *)
      | (true, i) => TryFunb tl func (* b.6 *)
      end
  end. 

Fixpoint TryFunb4 (l : list N)(b : N)(u : N)(func : N -> N -> option bool) : (bool * N) :=
  match l with
  | [] => (false, 0) (* b.5 *)
  | i :: tl =>
      let b2 := (N.square b) mod u in
        match func i b2 with
        | Some result => (result, i)
        | None => TryFunb4 tl b2 u func
        end
  end.

Fixpoint NInterval (low : N)(high : N) : list N :=
  map (N.add low) (Nlist (high + 1 - low)).

Print N. 

(* Returns (v, w) so that m = 2 ^ v * w and w is odd *)
Fixpoint Decom_tail (n : positive)(v : N) : N * positive :=
  match n with
  | xH => (v, xH)
  | xI _ => (v, n)
  | xO n' => Decom_tail n' (v + 1)
  end. 

Definition Decom (m : N) : N * N :=
  match m with
  | N0 => (0, 0)
  | Npos n => 
      match Decom_tail n N0 with
      | (v, w) => (v, Npos w)
      end
  end. 

Compute Decom 6. 
Compute Decom 24. 


(*B.1.10 u is odd and T is positive. If returns true then u is a ProbPrime.
* If Returns false then u is a composite.  *)
Definition ProPrimTest_debug (T : N)(u : N) : (bool * N * N * N * N * N * N) :=
  let m := u - 1 in
  let (v, w) := Decom m in (
  TryFunb (NInterval 1 T) 
  (fun j =>
    let a := SampleN 2 m j in
    let b := (a ^ w) mod u in
    if orb (N.eqb b 1) (N.eqb b m) then (true, j) (* b.3 *) else
      TryFunb4 (NInterval 1 (v - 1)) b u (* b.4 *)
      (fun i b2 =>
          if N.eqb b2 m then Some true else (* b.4.2 *)
          if N.eqb b2 1 then Some false else (* b.4.3 *)
          None (* b.4.4 *)
      )
  ), u, m, v, w). 

Definition ProPrimTest (T : N)(u : N) : bool :=
  match ProPrimTest_debug T u with
  | (result, _, _, _, _, _, _) => result
  end.
(*
Compute map (ProPrimTest_debug 999) (NInterval 3 99). (* 100% Correct *)
*)

(* From C.2 Example 1 *)
Definition constant_a := HexString.to_N "0xBB8E5E8FBC115E139FE6A814FE48AAA6F0ADA1AA5DF91985". 
Definition constant_p := HexString.to_N "0xBDB6F4FE3E8B1D9E0DA8C0D46F4C318CEFE4AFE3B6B8551F". 
 
Compute constant_a. 
(* true if passed the test, i.e. not singular *)
Definition SingTest (a b p : N) : bool :=
 negb (4 * (power a 3 p) + 27 * (square b) =? 0). 
(* D.1.1 method 2, true if this tuple is valid*)
Definition CheckSEED (SEED : bL)(a p : N) : option (bL * N * N) :=
  (*if Nat.leb (List.length SEED) 191%nat then None else*)
  let b := (HashN SEED) mod p in 
    if negb (SingTest a b p) then None
    else Some (SEED, a, b). 

Fixpoint GenSab_tail (seedl : list bL)(a p : N) : option (bL * N * N) :=
  match seedl with
  | [] => None
  | h :: tl =>
      match CheckSEED h a p with
      | Some tuple => Some tuple
      | None => GenSab_tail tl a p
      end
  end. 

Definition constant_seedlist := map 
  (fun x => N2bL_len x 192) [0; 1; 2 ^ 90; 2 ^ 191]. 
Compute constant_seedlist. 

Definition GenSab (a p : N) : option (bL * N * N) :=
  GenSab_tail constant_seedlist a p. 

Definition DisplaySab (para : option (bL * N * N)) :=
  match para with
  | None => ("", "", "")
  | Some (SEED, a, b) => (bS2hS (bL2bS SEED), HexString.of_N a, HexString.of_N b)
  end. 

Compute DisplaySab (GenSab constant_a constant_p). 

(* D.2.1 method 2 *)
Definition VeriSab (SEED : bL)(b p : N) : bool :=
  b =? (HashN SEED) mod p. 

Definition constant_T := 999. 

(* Test whether (xG, yG) is on the elliptic-curve defined by a b q *)
Definition OnCurveTest (xG yG a b p : N) : bool :=
  (square yG) mod p =? (xG ^ 3 + a * xG + b) mod p.  

Print nat. 

(* Prime field element: O or coordinated point *)
Inductive FEp : Set :=
  InfO : FEp | Cop : N * N -> FEp. 

Definition pf_eqb (P1 P2 : FEp) : bool :=
  match P1, P2 with
  | InfO, InfO => true
  | InfO, _ => false
  | _, InfO => false
  | Cop (x1, y1), Cop (x2, y2) =>
      andb (x1 =? x2) (y1 =? y2)
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

(* Identical *)
Compute map (fun x => pf_mul (Cop (1, 2)) x 17 3) (Nlist 9). 
Compute map (fun x => pf_mul_naive (Cop (1, 2)) (N.to_nat x) 17 3) (Nlist 9). 

(* Example 3 *)
Compute pf_add (Cop (10, 2)) (Cop (9, 6)) 19 1. (* Correct *)
Compute pf_mul (Cop (10, 2)) 2 19 1. (* Correct *)

Compute negb (3 =? 2). 

(* A.4.2.1, true means pass *)
(* j = B - i + 1 *)
Fixpoint MOV_Test_tail (j : nat)(q n : N)(acc : list (bool * N)) : list (bool * N)  :=
  match j with
  | O => acc (* i = B + 1, break *) 
  | S j' =>
      match acc with
      | [] => [] (*which will not happen*)
      | (b_old, t_old) :: tl =>
        let t := (t_old * q) mod n in
        let b := andb b_old (negb (t =? 1)) in
          MOV_Test_tail j' q n ((b, t) :: acc)
      end
  end. 

(* n is a prime and q is a prime exponent *)
Definition MOV_Test (B : nat)(q n : N) : bool :=
  fst (List.hd (false, 0) (MOV_Test_tail B q n [(true, 1)])). 

Definition constant_B := 27%N. 

(* A.4.2.2, true means pass *)
Definition Anomalous_Curve_Test (p order: N) : bool :=
  negb (p =? order). 

(* 5.2.2 returns None if valid, otherwise Some error message*)
(* Quick tests for large inputs *)
Definition VeriSysPara_Quick (p a b xG yG n : N)(SEED : bL) : option string :=
  if even p then Some "p is even." else
  if p <=? a then Some "a >= p" else
  if p <=? b then Some "b >= p" else
  if p <=? xG then Some "xG >= p" else
  if p <=? yG then Some "yG >= p" else
  let SEED_len := (N.of_nat (List.length SEED)) in
  if andb (0 <? SEED_len) (SEED_len <? 192) then Some "SEED is shorter than 192." else
  if andb (0 <? SEED_len ) (negb (VeriSab SEED b p)) then Some "Failed in VeriSab." else
  if negb (SingTest a b p) then Some "Failed in SingTest." else
  if negb (OnCurveTest xG yG a b p) then Some "Failed in OnCurveTest." else
  if n <=? N.shiftl 1 191 then Some "n <= 2 ^ 192." else
  if square n <=? 16 * p then Some "n <= 4 p ^ 1/2." else
  None. 

(* These tests are quite time consuming *)
Definition VeriSysPara (p a b xG yG n : N)(SEED : bL) : option string :=
  match VeriSysPara_Quick p a b xG yG n SEED with
  | Some msg => Some msg
  | None =>
    if negb (pf_eqb (pf_mul (Cop (xG, yG)) n p a) InfO) then Some "[n]G != O." else
    if negb (ProPrimTest p constant_T) then Some "p is a composite." else
    if negb (ProPrimTest n constant_T) then Some "n is a composite." else
    (* TODO need to understand these 
    if andb (negb (h =? 0)) (negb (h =? (F_div (square((square_root p) + 1) n p))))
      then Some "h != h'." else
    if negb (MOV_Test constant_B p  and Anomalous *)
    None
  end.

(*
Module tests. 

(* C.2 *)
(* Example 1 *)
Timeout 60 Compute 
let p := hS2N "BDB6F4FE3E8B1D9E0DA8C0D46F4C318CEFE4AFE3B6B8551F" in
let a := hS2N "BB8E5E8FBC115E139FE6A814FE48AAA6F0ADA1AA5DF91985" in
let b := hS2N "1854BEBDC31B21B7AEFC80AB0ECD10D5B1B3308E6DBF11C1" in
let xG := hS2N "4AD5F7048DE709AD51236DE65E4D4B482C836DC6E4106640" in
let yG := hS2N "02BB3A02D4AAADACAE24817A4CA3A1B014B5270432DB27D2" in
let n := hS2N "BDB6F4FE3E8B1D9E0DA8C0D40FC962195DFAE76F56564677" in
  VeriSysPara_Quick p a b xG yG n []
. (* None *)

(* Example 2 *)
Timeout 60 Compute 
let p := hS2N "8542D69E4C044F18E8B92435BF6FF7DE457283915C45517D722EDB8B08F1DFC3" in
let a := hS2N "787968B4FA32C3FD2417842E73BBFEFF2F3C848B6831D7E0EC65228B3937E498" in
let b := hS2N "63E4C6D3B23B0C849CF84241484BFE48F61D59A5B16BA06E6E12D1DA27C5249A" in
let xG := hS2N "421DEBD61B62EAB6746434EBC3CC315E32220B3BADD50BDC4C4E6C147FEDD43D" in
let yG := hS2N "0680512BCBB42C07D47349D2153B70C4E5D7FDFCBFA36EA1A85841B9E46E09A2" in
let n := hS2N "8542D69E4C044F18E8B92435BF6FF7DD297720630485628D5AE74EE7C32E79B7" in
  VeriSysPara_Quick p a b xG yG n []
. (* None *)

End tests. 
*)
