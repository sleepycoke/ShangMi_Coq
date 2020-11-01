Require Export Signature. 
(* TODO Should we imp a general hash_v here? 
ignored for now *)
(* j = ceil(klen/v) - i, from ceil(klen/v) - 1 to 0 *)
(* i from 1 to ceil(klen/v), ct = NtobL_len 32 i*)
(* TODO though klen/v could be as long as 2^32, 
I choose to use nat for 
 simplicity, which suffices for the tests, aka 128 klen *)
(* Returns a reversed HaList *)
(* hash_v returns a bL of length v *)
Section keyex_sec.

Context {U : Type}{fd : ECField U}
  (hash_v : bL -> bL)(v : nat)(klen : nat)(crv : ECurve). 
Definition grp := GE fd. 
Definition ftobl := FieldtobL crv. 

Fixpoint ComputeHaList (j : nat)(i : N)(Z : bL)
  (acc : list bL){struct j} :=
  let HaList := hash_v (Z ++ (NtobL_len 32 i)) :: acc in
  match j with
  | O => HaList 
  | S j' => 
      ComputeHaList j' (i + 1) Z HaList
  end. 

(* K = k || Ha! *)
Fixpoint Computek (HaList' : list bL)(acc : bL) : bL :=
  match HaList' with
  | [] => acc
  | h :: tl => Computek tl (acc ++ h)
  end. 

Definition KDF (Z : bL) : bL :=
  let HaList := 
    ComputeHaList ((div_ceil_nat klen v) - 1) 1 Z 
      [] in
  match HaList with
  | [] => [] (*HaList should not be empty *)
  | HaLast :: tl =>
    let HaiEx := 
      if Nat.eqb (Nat.modulo klen v) 0 then HaLast
      else 
      subList 0 (klen - v * (Nat.div klen v)) HaLast in
        (Computek tl []) ++ HaiEx
  end. 

(* A1 - A3 *)
Definition ComputeR (G : grp)(r : N) : grp :=
  match crv with
  | pf_curve a _ _ => pf_mul a G r
  | bf_curve a _ _ => pf_mul a G r (*TODO bf*)
  end. 

Definition ComputeTilde (w : N)(x : U) : N :=
      let w2 := N.shiftl 1 w in
      w2 + (N.land (uwp x) (w2 - 1) ). 

Definition ComputeW (n : N) : N :=
  (div_ceil_N (N.size (n - 1)) 2) - 1.

(*B1 - B9*)
Definition ComputeV (ml : grp -> N -> grp)
  (ad : grp -> grp -> grp)(n h t x_tilde  : N)
  (P R : grp): grp :=
  ml (ad P (ml R x_tilde)) (P_mul n h t). 

Open Scope N_scope.
Definition ComputeK (x y : U)(ZA ZB : bL) : bL :=
  KDF ((FieldtobL crv x) ++ (FieldtobL crv y) ++ ZA ++ ZB). 

Definition ComputeS (prehS : string)(ZA ZB : bL)
    (x y x1 y1 x2 y2 : U) : bL :=
    hash_v ((hStobL prehS) ++ (ftobl y) ++ 
    (hash_v ((ftobl x) ++ ZA ++ ZB ++ (ftobl x1) ++ 
    (ftobl y1) ++ (ftobl x2) ++ (ftobl y2)))). 

(* A5 *)
Definition ComputeT (n d x_tilde r : N) : N :=
 P_add n d (x_tilde * r). 
Definition ComputeRBKBSB (*(comk : (bL -> bL) -> nat -> nat -> N 
    -> N -> bL -> bL -> bL)
    (coms : (bL -> bL) -> string -> bL -> bL -> N -> N
     -> N -> N -> N -> N -> bL)*)(ml : grp -> N -> grp)
     (ad : grp -> grp -> grp)(G : grp)(n h : N)
      (ZA ZB : bL)(RA PA : grp)(rB dB : N) : optErr (grp * bL * bL) :=
  let RB := ComputeR G rB in 
  match RB with
  | InfO _ => Error "RB = InfO"(* impossible since rB < n *)
  | Cop _ (x2, y2) =>
      (* w2 := 2^w < n by definiton of w *)
      let w := ComputeW n in
      let x2_tilde := ComputeTilde w x2 in
      let tB := ComputeT n dB x2_tilde rB in
      (* B5 *)
      match RA with
      | InfO _ => Error "RA = InfO"
      | Cop _ (x1, y1) => 
      if negb (OnCurve crv x1 y1) 
      then Error "RA is not on the curve" else 
        let x1_tilde := ComputeTilde w x1 in
        (* B6 *)
        let V := ComputeV ml ad n h tB x1_tilde PA RA in
        match V with
        | InfO _ => Error "V = InfO"
        | Cop _ (xV, yV) =>
            (* B7 *)
            let KB := ComputeK xV yV ZA ZB in
            (* B8 *)
            let SB := ComputeS "02" ZA ZB xV yV x1 y1 x2 y2 in
            Normal (RB, KB, SB)
        end
      end
  end.
(*
Definition ComputeRBKBSB_pf (hash_v : bL -> bL)(v : nat)
(klen : nat)(p a b : N)(G : grp)(n h : N)(ZA ZB : bL)
(RA PA : grp)(rB dB : N) : optErr (grp * bL * bL) :=
  ComputeRBKBSB hash_v v klen (ComputeK 0) (ComputeS 0) 
  (pf_mul p a) (pf_add p a) (OnCurve_pf p a b)
    G n h ZA ZB RA PA rB dB . 

Definition ComputeRBKBSB_bfp (hash_v : bL -> bL)(v : nat)
(klen : nat)(m gp a b : N) (G : grp)(n h : N)(ZA ZB : bL)
(RA PA : grp)(rB dB : N): optErr (grp * bL * bL) :=
  ComputeRBKBSB hash_v v klen (ComputeK m) (ComputeS m) 
  (bfp_mul m gp a) (bfp_add m gp a) (OnCurve_bfp gp a b)
   G n h ZA ZB RA PA rB dB. 
*)

(* A4-A10 *)
Definition ComputeKAS1SA (*(hash_v : bL -> bL)(v : nat)
(klen : nat)(comk : (bL -> bL) -> nat ->nat -> N -> N 
-> bL -> bL -> bL)(coms : (bL -> bL) -> string -> bL 
-> bL -> N -> N -> N -> N -> N -> N -> bL)*)
(ml : grp -> N -> grp)(ad : grp -> grp -> grp)
(*(OnCrv : N -> N -> bool)*)
(rA dA n h : N) (PB RA RB : grp)(ZA ZB SB : bL)
: optErr (bL * bL * bL) :=
  match RA with
  | InfO _ => Error "RA = InfO"
  | Cop _ (x1, y1) =>
      let w := ComputeW n in
      let x1_tilde := ComputeTilde w x1 in
      let tA := ComputeT n dA x1_tilde rA in
      match RB with
      (*RB cannot be InfO since rB < n*)
      | InfO _ => Error "RB = InfO" 
      | Cop _ (x2, y2) =>
        if negb (OnCurve crv x2 y2) 
          then Error "RB is not on curve"
        else let x2_tilde := ComputeTilde w x2 in
        let U := ComputeV ml ad n h tA x2_tilde PB RB in  
        match U with
        | InfO _ => Error "U = InfO"
        | Cop _ (xU, yU) =>
            let KA := ComputeK xU yU ZA ZB in
            let S1 := 
              ComputeS "02" ZA ZB xU yU x1 y1 x2 y2 in
            if negb (bLeqb S1 SB) then Error "S1 != SB"
            else let SA := 
              ComputeS "03" ZA ZB xU yU x1 y1 x2 y2 in
              Normal (KA, S1, SA)
        end
      end
  end. 

(*Definition ComputeKAS1SA_pf (hash_v : bL -> bL)(v : nat)
(klen : nat)(p a b : N) (rA dA n h : N) (PB RA RB : grp)
(ZA ZB SB : bL): optErr (bL * bL * bL) :=
  ComputeKAS1SA  hash_v v klen (ComputeK 0) (ComputeS 0)
   (pf_mul p a) (pf_add p a) (OnCurve_pf p a b)
rA dA n h PB RA RB ZA ZB SB. 

Definition ComputeKAS1SA_bfp (hash_v : bL -> bL)(v : nat)
(klen : nat)(m gp a b : N) (rA dA n h : N) (PB RA RB : grp)
(ZA ZB SB : bL): optErr (bL * bL * bL) :=
  ComputeKAS1SA hash_v v klen (ComputeK m) (ComputeS m) 
  (bfp_mul m gp a) (bfp_add m gp a) (OnCurve_bfp gp a b)
rA dA n h PB RA RB ZA ZB SB. 
*)

(* B10 *)
Definition VeriS2eqSA (*(hash_v : bL -> bL)
(coms : (bL -> bL) -> string -> bL -> bL -> N -> N -> N 
-> N -> N -> N -> bL)*)(ZA ZB SA: bL)
(xV yV x1 y1 x2 y2 : U) : bool :=
  let S2 := ComputeS "03" ZA ZB xV yV x1 y1 x2 y2 in
    bLeqb S2 SA. 
(*Definition VeriS2eqSA_pf (*(hash_v : bL -> bL)*)(ZA ZB SA: bL)
(xV yV x1 y1 x2 y2 : N) : bool :=
  VeriS2eqSA hash_v (ComputeS 0) ZA ZB SA xV 
    yV x1 y1 x2 y2. *)

End keyex_sec.
