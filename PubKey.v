Require Export KeyEx.

Locate pf_mul. 
(*A2 - A5 *)
Fixpoint All0bL (bl : bL) : bool :=
  match bl with
  | [] => true
  | true :: tl => false
  | false :: tl =>
      All0bL tl
  end. 
 
Compute
let (a, b) := (1, 2) in (a, b). 

Definition TryComputeTwithK (k p a h : N)(cp : cmp_type)(G PB : FEp)
 (klen : nat)(hash_v : bL -> bL)(v : nat) : optErr (option (bL * bL * bL * bL)) :=
  let C1 := pf_mul G k p a in
  match C1 with
  | InfO => Error "C1 = InfO" (* impossible since k < n *)
  | Cop (x1, y1) =>
    let C1bl := BL2bL (Point2BL_p x1 y1 cp) in
    let S := pf_mul PB h p a in
    match S with
    | InfO => Error "S = InfO"
    | _ =>
        let kPB := pf_mul PB k p a in
        match kPB with
        | InfO => Error "kPB = InfO" (* impossible since k < n *)
        | Cop (x2, y2) => 
          let (x2bl, y2bl) := (N2BbL x2, N2BbL y2) in
          let t := KDF(x2bl ++ y2bl) klen hash_v v in
           if All0bL t then Normal None
           else Normal (Some (t, x2bl, y2bl, C1bl))
        end
    end
  end. 

(* a and b should be of the same length *)
Fixpoint bLXOR_tail (a b acc : bL) : bL :=
  match a, b with
  | ha :: ta, hb :: tb =>
       bLXOR_tail ta tb ((xorb ha hb) :: acc)
  | [], _ => acc
  | _, [] => acc
  end. 

Definition bLXOR (a b : bL) :=
  rev (bLXOR_tail a b []).

Definition M := hS2bL "656E63 72797074 696F6E20 7374616E 64617264". 
Definition t := hS2bL "983BCF 106AB2DC C92F8AEA C6C60BF2 98BB0117". 
Compute bL2hS (bLXOR M t). (*Correct*)

Fixpoint ComputeCwithklist (M : bL)(klist : list N)(p a h : N)(cp : cmp_type)
  (G PB : FEp)(hash_v : bL -> bL)(v : nat) : optErr bL :=
  match klist with
  | [] => Error "klist depleted"
  | k :: tl =>
      match TryComputeTwithK k p a h cp G PB (length M) hash_v v with
      | Error err => Error (err ++ " k = " ++ (N2hS k))
      | Normal None =>
          ComputeCwithklist M tl p a h cp G PB hash_v v
      | Normal (Some (t, x2bl, y2bl, C1bl)) =>
          let C2 := bLXOR M t in
          let C3 := hash_v (x2bl ++ M ++ y2bl) in
            Normal (C1bl ++ C2 ++ C3)
      end
  end. 
          






