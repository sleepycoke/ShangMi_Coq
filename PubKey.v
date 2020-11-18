Require Export KeyEx.

Section pubkey_sec.
Context {U : Type}{fd : ECField U}
  (hash_v : bL -> bL)(v : nat)(klen : nat)(crv : ECurve). 
(*A2 - A5 *)
Definition TryComputeTwithK 
  (ml : grp -> N -> grp)(ptobL : grp -> bL)
    (k h : N) (G PB : grp) : optErr (option (bL * bL * bL * bL)) :=
  let C1 := ml G k in
  match C1 with
  | InfO _ => Error "C1 = InfO _" (* impossible since k < n *)
  | _ =>
    let C1bl := ptobL C1 in
    let S := ml PB h in
    match S with
    | InfO _ => Error "S = InfO _"
    | _ =>
        let kPB := ml PB k in
        match kPB with
        | InfO _ => Error "kPB = InfO _" (* impossible? *)
        | Cop _ (x2, y2) => 
          let (x2bl, y2bl) := (NtoBbL (uwp x2), NtoBbL (uwp y2)) in
          let t := KDF hash_v v klen (x2bl ++ y2bl) in
           if All0bL t then Normal None
           else Normal (Some (t, x2bl, y2bl, C1bl))
        end
    end
  end. 

(* A1 - A8 *)
Fixpoint ComputeCwithklist_fix (ml : grp -> N -> grp)
  (p2bL : grp -> bL)(h : N)(klist : list N)
  (G PB : grp)(M : bL) : optErr bL :=
  match klist with
  | [] => Error "klist depleted"
  | k :: tl =>
      match TryComputeTwithK ml p2bL k h G PB  with
      | Error err => Error (err ++ " k = " ++ (NtohS k))
      | Normal None =>
          ComputeCwithklist_fix ml p2bL h tl G PB M
      | Normal (Some (t, x2bl, y2bl, C1bl)) =>
          let C2 := bLXOR M t in
          let C3 := hash_v (x2bl ++ M ++ y2bl) in
            Normal (C1bl ++ C2 ++ C3)
      end
  end. 

Definition ComputeCwithklist (h : N)(klist : list N)(cp : cmp_type)(G PB : grp)
  (M : bL) : optErr bL :=             
  let (ml,  ptobL) :=
  match crv with
  | pf_curve a _ _ => (pf_mul a, Point2bL cp)
  | bf_curve a _ _ => (pf_mul a, Point2bL cp) (*TODO bf case*)
  end in
    ComputeCwithklist_fix ml ptobL h klist G PB M. 

(*Definition ComputeCwithklist_pf (hash_v : bL -> bL)(v : nat)(p a h : N)(klist : list N)(cp : cmp_type)(G PB : GE)(M : bL) : optErr bL :=
  ComputeCwithklist hash_v v (pf_mul p a) (Point2BL_p cp) NtoBbL h klist G PB M. 

Definition ComputeCwithklist_bfp (hash_v : bL -> bL)(v : nat)(m gp a h : N)(klist : list N)(cp : cmp_type)(G PB : GE)(M : bL) : optErr bL :=
  ComputeCwithklist hash_v v (bfp_mul m gp a) (Point2BL_b m cp) (NtoBbL_len (N.to_nat m)) h klist G PB M. 
  *)

(* B1 - B7 *)
(* q is the size of the field *)
Definition ComputeM' (cp : cmp_type)(crv : ECurve)(q : N)(h dB : N)(C : bL)
   : optErr bL :=
  let (ml, _) := ml_ad_extractor crv in
  let (C1bL, C2C3bL) := partListBack C (Nat.add klen v) in
  match BLtoPoint cp q crv (bLtoBL C1bL) with
  | None => Error "Failed to uncompress C1"
  | Some C1 =>
    if negb (OnCurve crv C1) then Error "C1 not on curve"
    else let S := ml C1 h in
    match S with
    | InfO _ => Error "S = InfO _"
    | _ =>
        let dBC1 := ml C1 dB in
        match dBC1 with
        | InfO _ => Error "dBC1 = InfO"
        | Cop _ (x2, y2) =>
            let (x2bL, y2bL) := (FieldtobL x2, FieldtobL y2) in
            let t := KDF hash_v v klen (x2bL ++ y2bL) in
            if All0bL t then Error "t is all 0s" else
            let (C2bL, C3bL) := partList C2C3bL klen in
            let M' := bLXOR C2bL t in
            let u := hash_v (x2bL ++ M' ++ y2bL) in
            if negb (bLeqb u C3bL) then Error "u != C3"
            else Normal M'
        end
    end
  end. 


(* B1 - B7 *)
(*Definition ComputeM' (ml : grp -> N -> grp)(Bl2p : BL -> option (N * N))
  (Ntobl : N -> bL)(h dB : N)(C : bL) : optErr bL :=
  let (C1bL, C2C3) := partListBack C (Nat.add klen v) in
  match Bl2p (bLtoBL C1bL) with
  | None => Error "Failed to uncompress C1"
  | Some (x1, y1) =>
    if negb (OnCrv x1 y1) then Error "C1 not on curve"
    else let C1 := Cop (x1, y1) in
    let S := ml C1 h in
    match S with
    | InfO => Error "S = InfO"
    | _ =>
        let dBC1 := ml C1 dB in
        match dBC1 with
        | InfO => Error "dBC1 = InfO"
        | Cop (x2, y2) =>
            let (x2bL, y2bL) := (Ntobl x2, Ntobl y2) in
            let t := KDF (x2bL ++ y2bL) klen hash_v v in
            if All0bL t then Error "t is all 0s" else
            let (C2, C3) := partList C2C3 klen in
            let M' := bLXOR C2 t in
            let u := hash_v (x2bL ++ M' ++ y2bL) in
            if negb (bLeqb u C3) then Error "u != C3"
            else Normal M'
        end
    end
  end. 
*)

(*Definition ComputeM'_pf (hash_v : bL -> bL)(v : nat)(klen : nat)(p a b h dB : N)(cp : cmp_type)(C : bL) : optErr bL :=
  ComputeM' hash_v v klen (pf_mul p a) (OnCurve_pf p a b) (BLtoPoint_p cp p a b) NtoBbL h dB C . 

Definition ComputeM'_bfp (hash_v : bL -> bL)(v : nat)(klen : nat)(m gp a b h dB : N)(cp : cmp_type)(C : bL) : optErr bL :=
  ComputeM' hash_v v klen (bfp_mul m gp a) (OnCurve_bfp gp a b) (BLtoPoint_bfp cp m gp a b) (NtoBbL_len (N.to_nat m)) h dB C . 
*)
End pubkey_sec. 
