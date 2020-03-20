Require Export ECAlg. 
Require Export SM3. 

(* TODO RANDOMLY sample a number in [low, high] *)
Definition SampleN (low : N)(high : N)(seed : N) : N :=
  low + (seed mod (high + 1 - low)). 

(*Compute map (SampleN 10 20) (Nlist 15). *)

(* Generally try each element in l until func returns false. Should all true returns true *)
Fixpoint Scrutinize (DomType : Type)(test : DomType -> bool)(l : list DomType) : bool :=
  match l with
  | [] => true
  | h :: tl =>
      match test h with
      | false => false
      | true => Scrutinize DomType test tl
      end
  end. 

Definition ScrutN (test : N -> bool)(l : list N): bool :=
  Scrutinize N test l. 

(* For B.1.10, false if composite *)
Definition TryFunb (func : N -> bool)(l : list N) : bool :=
  ScrutN func l.  
(*
  match l with
  | [] => true
  | j :: tl =>
      match func j with
      | false => false (* b.5 *)
      | true => TryFunb tl func (* b.6 *)
      end
  end. 
*)
(*
Fixpoint TryFunb (l : list N)(func : N -> (bool * N)) : (bool * N * N) :=
  match l with
  | [] => (true, 0, 0)
  | j :: tl =>
      match func j with
      | (false, i) => (false, j, i) (* b.5 *)
      | (true, i) => TryFunb tl func (* b.6 *)
      end
  end. 
*)
Fixpoint TryFunb4 (b u : N)(func : N -> N -> option bool)(l : list N) : bool :=
  match l with
  | [] => false (* b.5 *)
  | i :: tl =>
      let b2 := (N.square b) mod u in
        match func i b2 with
        | Some result => result
        | None => TryFunb4 b2 u func tl
        end
  end.

Fixpoint NInterval (low : N)(high : N) : list N :=
  map (N.add low) (Nlist (high + 1 - low)).

(* Returns (v, w) so that m = 2 ^ v * w and w is odd *)
Fixpoint Decom_tail (v : N)(n : positive) : N * positive :=
  match n with
  | xH => (v, xH)
  | xI _ => (v, n)
  | xO n' => Decom_tail (v + 1) n'
  end. 

Definition Decom (m : N) : N * N :=
  match m with
  | N0 => (0, 0)
  | Npos n => 
      match Decom_tail N0 n with
      | (v, w) => (v, Npos w)
      end
  end. 


(*B.1.10 u is odd and T is positive. If returns true then u is a ProbPrime.
If Returns false then u is a composite.  *)
(* TODO NInterval is too long in memory *)
Definition ProPrimTest (T : N)(u : N) : bool :=
  let m := u - 1 in
  let (v, w) := Decom m in (
  TryFunb  
  (fun j =>
    let a := SampleN 2 m j in
    let b := (a ^ w) mod u in
    if orb (N.eqb b 1) (N.eqb b m) then true (* b.3 *) else
      TryFunb4 b u  (* b.4 *)
      (fun i b2 =>
          if N.eqb b2 m then Some true else (* b.4.2 *)
          if N.eqb b2 1 then Some false else (* b.4.3 *)
          None (* b.4.4 *)
      ) (NInterval 1 (v - 1)))
  )
  (NInterval 1 T). 


(*
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
*)
(*
Compute map (ProPrimTest_debug 999) (NInterval 3 99). (* 100% Correct *)
*)

(* From C.2 Example 1 *)
Definition constant_a := HexString.to_N "0xBB8E5E8FBC115E139FE6A814FE48AAA6F0ADA1AA5DF91985". 
Definition constant_p := HexString.to_N "0xBDB6F4FE3E8B1D9E0DA8C0D46F4C318CEFE4AFE3B6B8551F". 
 
(* true if passed the test, i.e. not singular *)
Definition SingTest (a b p : N) : bool :=
 negb (4 * (P_power a 3 p) + 27 * (square b) =? 0). 
(* D.1.1 method 2, true if this tuple is valid*)
Definition CheckSEED (SEED : bL)(a p : N) : option (bL * N * N) :=
  (*if Nat.leb (List.length SEED) 191%nat then None else*)
  let b := (HashN SEED) mod p in 
    if negb (SingTest a b p) then None
    else Some (SEED, a, b). 

Fixpoint GenSab_tail (p a : N)(seedl : list bL) : option (bL * N * N) :=
  match seedl with
  | [] => None
  | h :: tl =>
      match CheckSEED h a p with
      | Some tuple => Some tuple
      | None => GenSab_tail p a tl
      end
  end. 

Definition constant_seedlist := map 
  (fun x => N2bL_len 192 x) [0; 1; 2 ^ 90; 2 ^ 191]. 

Definition GenSab (a p : N) : option (bL * N * N) :=
  GenSab_tail p a constant_seedlist. 

Definition DisplaySab (para : option (bL * N * N)) :=
  match para with
  | None => ("", "", "")
  | Some (SEED, a, b) => (bS2hS (bL2bS SEED), HexString.of_N a, HexString.of_N b)
  end. 


(* D.2.1 method 2 *)
Definition VeriSab (p b : N)(SEED : bL) : bool :=
  b =? (HashN SEED) mod p. 

Definition constant_T := 999. 


(* A.4.2.1, true means pass *)
(* j = B - i + 1 *)
Fixpoint MOV_Test_tail (q n : N)(j : nat)(acc : list (bool * N)) : list (bool * N)  :=
  match j with
  | O => acc (* i = B + 1, break *) 
  | S j' =>
      match acc with
      | [] => [] (*which will not happen*)
      | (b_old, t_old) :: tl =>
        let t := (t_old * q) mod n in
        let b := andb b_old (negb (t =? 1)) in
          MOV_Test_tail q n j' ((b, t) :: acc)
      end
  end. 

(* n is a prime and q is a prime exponent *)
Definition MOV_Test (B: nat)(q n : N) : bool :=
  fst (List.hd (false, 0) (MOV_Test_tail q n B [(true, 1)])). 

Definition constant_B := 27%nat. 

(* A.4.2.2, true means pass *)
Definition Anomalous_Curve_Test (p order: N) : bool :=
  negb (p =? order). 

(* floor(2*sqrt(p)) *)
Definition floor2sqrt(p : N) : N :=
  let r2 := N.double (N.sqrt p) in
  if r2 =? N.sqrt (p * 4) then r2 else r2 + 1. 

Definition Computeh' (p n : N) : N :=
  N.div (p + 1 + (floor2sqrt p)) n. 
(* 5.2.2 returns None if valid, otherwise Some error message*)
(* Quick tests for large inputs *)
Definition VeriSysPara_Quick (p a b n h xG yG order : N)(SEED : bL) : option string :=
  if even p then Some "p is even." else
  if p <=? a then Some "a >= p" else
  if p <=? b then Some "b >= p" else
  if p <=? xG then Some "xG >= p" else
  if p <=? yG then Some "yG >= p" else
  let SEED_len := (N.of_nat (List.length SEED)) in
  if andb (0 <? SEED_len) (SEED_len <? 192) then Some "SEED is shorter than 192." else
  if andb (0 <? SEED_len ) (negb (VeriSab p b SEED)) then Some "Failed in VeriSab." else
  if negb (SingTest p a b) then Some "Failed in SingTest." else
  if negb (OnCurve_pf p a b xG yG) then Some "Failed in OnCurveTest." else
  if n <=? N.shiftl 1 191 then Some "n <= 2 ^ 192." else
  if square n <=? 16 * p then Some "n <= 4 p ^ 1/2." else
  if negb (h =? Computeh' p n) then Some "h != h'." else
  None. 

(* These tests are quite time consuming *)
Definition VeriSysPara (p a b n h xG yG order: N)(SEED : bL) : option string :=
  match VeriSysPara_Quick p a b n h xG yG order SEED with
  | Some msg => Some msg
  | None =>
    if negb (GE_eqb (pf_mul p a (Cop (xG, yG)) n) InfO) then Some "[n]G != O." else
    if negb (ProPrimTest constant_T p) then Some "p is a composite." else
    if negb (ProPrimTest constant_T n)  then Some "n is a composite." else
    if negb (MOV_Test constant_B p n ) then Some "Failed in MOV test" else 
    if negb (Anomalous_Curve_Test p order) then Some "Failed in Anomalous Curve Test" else
    None
  end.
Module tests. 

(*
(* C.2 *)
(* Example 1 *)
Time Compute 
let p := hS2N "BDB6F4FE3E8B1D9E0DA8C0D46F4C318CEFE4AFE3B6B8551F" in
let a := hS2N "BB8E5E8FBC115E139FE6A814FE48AAA6F0ADA1AA5DF91985" in
let b := hS2N "1854BEBDC31B21B7AEFC80AB0ECD10D5B1B3308E6DBF11C1" in
let xG := hS2N "4AD5F7048DE709AD51236DE65E4D4B482C836DC6E4106640" in
let yG := hS2N "02BB3A02D4AAADACAE24817A4CA3A1B014B5270432DB27D2" in
let n := hS2N "BDB6F4FE3E8B1D9E0DA8C0D40FC962195DFAE76F56564677" in
let h := 1 in (*By Hasse Thm*)
let order := 1 in (*There is no way for me to know it, just assign it to test*)
  VeriSysPara_Quick p a b n h xG yG order []

. (* None *)

(* Example 2 *)
Time Compute 
let p := hS2N "8542D69E4C044F18E8B92435BF6FF7DE457283915C45517D722EDB8B08F1DFC3" in
let a := hS2N "787968B4FA32C3FD2417842E73BBFEFF2F3C848B6831D7E0EC65228B3937E498" in
let b := hS2N "63E4C6D3B23B0C849CF84241484BFE48F61D59A5B16BA06E6E12D1DA27C5249A" in
let xG := hS2N "421DEBD61B62EAB6746434EBC3CC315E32220B3BADD50BDC4C4E6C147FEDD43D" in
let yG := hS2N "0680512BCBB42C07D47349D2153B70C4E5D7FDFCBFA36EA1A85841B9E46E09A2" in
let n := hS2N "8542D69E4C044F18E8B92435BF6FF7DD297720630485628D5AE74EE7C32E79B7" in
let h := 1 in (*By Hasse Thm*)
let order := 1 in (*There is no way for me to know it, just assign it to test*)
  VeriSysPara_Quick p a b n h xG yG order []
. (* None *)

End tests. 
*)

(* B.2.4, Irredicible Polynomial Test*)
(* j = d/2 - i *)
Fixpoint IrdBody (sq : N -> N)(gcd : N -> N -> N)(f u' : N)(j : nat) : bool :=
  match j with
  | O => true
  | S j' =>
    let u := B_mod (sq u') f in
    let g := gcd (B_add u 2) f in
      if N.eqb g 1 then IrdBody sq gcd f u j'
        else false
  end. 

Definition IrdTest (f : N) : bool :=
  let d := size_nat f in
  let u := 2%N in
    IrdBody (Bp_sq_raw) B_gcd f u (Nat.div d 2). 

(*
(* TODO need test casess *)

Compute IrdTest  37. (* Correct  *)

Compute List.length []. 

Print map. 

Compute map N.double [2; 3]. 

Definition TPB_list := map decode_TPB TPB_IRP. 
 
(*Compute map IrdTest (TPB_list). All true, correct *)
Definition PPB_list := map decode_PPB PPB_IRP. 
(*Time Compute map IrdTest (PPB_list).*) (*Finished transaction in 393.439 secs (393.19u,0.153s) (successful)All true, correct *)
*)
End tests. 
