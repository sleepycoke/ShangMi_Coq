Require Export SM2_DataType. 

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

Compute map (ProPrimTest_debug 999) (NInterval 3 99). (* 100% Correct *)

