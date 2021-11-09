(*Require Export SysPara.*)
Require Export SM3. 
Require Export ECAlg.

(*5.5 trunk from right *)
(*TODO I really cannot understand its definition *)
Definition ENTL (ID : bL) :=
  NtobL_len 16 (N.of_nat (List.length (ID))). 

Open Scope list. 

Section signature_sec. 

Context {U : Type}{fd : ECField U}. 
Variable hash : bL -> bL. 
Definition grp := GE fd. 

Definition cop := Cop fd.

Definition ComputeZ (ENTL_A ID_A a b xG yG xA yA : bL) :=
  hash (ENTL_A ++ ID_A ++ a ++ b ++ xG ++ yG ++ xA ++ yA).

Section gml_sec.
Variable gml : grp -> N -> grp. 

Definition TrySigWithk (G : grp)(n dA e k : N)
   : option (N * N) := 
  match gml G k with
  | InfO _ => None
  | Cop _ (x1, y1) => 
      let r := P_add n e (uwp x1) in
        if orb (N.eqb r 0) (N.eqb (r + k) n) then None else
        let s := P_mul n (P_inv n (P_add n 1 dA)) (P_sub n k (P_mul n r dA)) in
          if N.eqb s 0 then None else
          Some (r, s)
  end. 

Fixpoint TrySigWithList (G : grp)(n dA e : N)(klist : list N) : option (N * N) :=
  match klist with
  | [] => None
  | h :: tl =>
      match TrySigWithk G n dA e h with
      | None => TrySigWithList G n dA e tl
      | Some (r, s) => Some (r, s)
      end 
  end. 

End gml_sec. 


(* 6.1 *)
(* TODO How to generate klist? *)
Definition SigWithList (curve : ECurve)
  (nbL xGbL yGbL ENTL_A ID_A dAbL xAbL yAbL M : bL)(klist : list N)
  : option (bL * (bL * bL)) :=
  let gml := 
    match curve with 
    | pf_curve a' _ _ => pf_mul a'
    (*| bf_curve a' _ _ => pf_mul a'*) (*TODO bf case*)
    end in
  let (a, b) := match curve with 
    | pf_curve a' b' _ (*| bf_curve a' b' _*) => (uwp a', uwp b')
  end in
  let Z_A := ComputeZ ENTL_A ID_A (NtoBbL a) (NtoBbL b) xGbL yGbL xAbL yAbL in
  let e := bLtoN (hash (Z_A ++ M)) in
    match TrySigWithList gml (GE_wp fd (bLtoN xGbL, bLtoN yGbL))
      (bLtoN nbL) (bLtoN dAbL) e klist with
      | None => None
      | Some (r, s) => Some (M, ((NtoBbL r), (NtoBbL s)))
    end.
    
(*

Definition SigWithList_pf (p a b n xG yG ENTL_A ID_A dA xA yA M : bL)(klist : list N)
   : option (bL * (bL * bL)) :=
   SigWithList hash (pf_mul (bLtoN p) (bLtoN a)) a b n xG yG ENTL_A ID_A dA xA yA M klist. 

Definition SigWithList_bfp (m gp : N)(a b n xG yG ENTL_A ID_A dA xA yA M : bL)(klist : list N)
   : option (bL * (bL * bL)) :=
   SigWithList hash (bfp_mul m gp (bLtoN a)) a b n xG yG ENTL_A ID_A dA xA yA M klist. 

Definition SigWithZAList_bfp (m gp : N)(a b n xG yG ZA dA xA yA M : bL)(klist : list N)
   : option (bL * (bL * bL)) :=
   SigWithZAList hash (bfp_mul m gp (bLtoN a)) a b n xG yG ZA dA M klist. 

*)
(* true if x \in [lower, upper] *)
Definition inRange (x lower upper : N) : bool :=
  andb (leb lower x) (leb x upper). 

Open Scope N_scope. 

(* None if passed, otherwise Some error message *)
Definition VeriSig_inner (gml : grp -> N -> grp)(gad : grp -> grp -> grp)
  (n xG yG xA yA r' s' : N)(Z_A M' : bL) : option string :=
  if negb (inRange r' 1 (n - 1)) then Some "r' out of range" else
  if negb (inRange s' 1 (n - 1)) then Some "s' out of range" else
  let e' := bLtoN (hash (Z_A ++ M')) in
  let t := P_add n r' s' in
  if t =? 0 then Some "t = 0" else 
  let G := GE_wp fd (xG, yG) in
  let PA := GE_wp fd (xA, yA) in
  match gad (gml G s') (gml PA t) with
  | InfO _ => Some "s'G + tPA = InfO"
  | Cop _ (x1', y1') => 
      let R := P_add n e' (uwp x1') in
      if R =? r' then None else Some "R != r'"
  end. 

Definition VeriSig (curve : ECurve)(n xG yG xA yA r' s' Z_A M' : bL)
 : option string :=
  let (gml, gad) := 
    match curve with 
    | pf_curve a _ _ => (pf_mul a, pf_add a)
    (*| bf_curve a _ _ => (pf_mul a, pf_add a)*) (*TODO bf case*)
    end in
  VeriSig_inner gml gad (bLtoN n) (bLtoN xG) (bLtoN yG)
   (bLtoN xA) (bLtoN yA) (bLtoN r') (bLtoN s') Z_A M'.

(*
Definition VeriSig_pf (p a n xG yG xA yA : N)(r'bL s'bL Z_A M' : bL) : option string :=
  VeriSig_inner (pf_mul p a) (pf_add p a) n xG yG xA yA r'bL s'bL Z_A M'. 

Definition VeriSig_bfp  (m gp a n xG yG xA yA : N)(r'bL s'bL Z_A M' : bL) : option string :=
  VeriSig hash (bfp_mul m gp a) (bfp_add m gp a) n xG yG xA yA r'bL s'bL Z_A M'. 
*)
End signature_sec. 