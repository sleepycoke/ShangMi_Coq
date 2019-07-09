Require Export SM2_DataType. 

(*B.1.10 u is odd and T is positive. If returns true then u is a ProbPrime.
* If Returns false then u is a composite.  *)
(* TODO RANDOMLY sample a number in [low, high] *)
Definition SampleN (low : N)(high : N) : N :=
  high - 1. 

(* false if composite *)
Fixpoint TryFunb (l : list N)(func : N -> bool) : bool :=
  match l with
  | [] => true
  | j :: tl =>
      match func j with
      | false => false (* b.5 *)
      | true => TryFunb tl func (* b.6 *)
      end
  end. 

Fixpoint TryFunb4 (l : list N)(b : N)(u : N)(func : N -> N -> option bool) : bool :=
  match l with
  | [] => false (* b.5 *)
  | i :: tl =>
      let b2 := (N.square b) mod u in
        match func i b2 with
        | Some result => result
        | None => TryFunb4 tl b2 u func
        end
  end.

Definition ProPrimTest (u : N)(T : N) : bool :=
  let m := u - 1 in
  let v := N.log2 m in
  let w := N.div m v in
  TryFunb (Nlist T) 
  (fun j =>
    let a := SampleN 2 m in
    let b := (a ^ w) mod u in
    if orb (N.eqb b 1) (N.eqb b m) then true (* b.3 *) else
      TryFunb4 (Nlist m) b u (* b.4 *)
      (fun i b2 =>
          if N.eqb b2 m then Some true else (* b.4.2 *)
          if N.eqb b2 1 then Some false else (* b.4.3 *)
          None (* b.4.4 *)
      )
  ). 
      
