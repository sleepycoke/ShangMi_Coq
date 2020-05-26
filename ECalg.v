Require Export ECDef. 
  
(*A.5.2*)
Definition tide_p (yp : N) : bool :=
  N.odd yp. 

(*B.1.3*)
Fixpoint Lucas_tail (p X Delta : N)(k : bL)(acc : N * N) : N * N :=
  match k with
  | [] => acc
  | ki :: tl =>
      match acc with (U0, V0) =>
        let (U1, V1) := 
            ((U0 * V0) mod p, (P_div p ((N.square V0) + Delta * (N.square U0))) 2) in
          match ki with
          | false => Lucas_tail p X Delta tl (U1, V1)
          | true => Lucas_tail p X Delta tl 
              ((P_div p (X * U1 + V1) 2), (P_div p (X * V1 + Delta * U1) 2)) 
          end
      end
  end.


(* X, Y > 0 *)
Definition Lucas (p X Y k : N) :=
  match NtobL k with
  | true :: k' => (* k > 0 *)
    Lucas_tail p X (((N.square X) + 4 * (p - Y)) mod p) k' (1, X)
  | _ => (0, 2) (* k = 0 *)
  end. 

Fixpoint Lucas_naive (X : Z)(Y : Z)(k : nat)(p : Z) {struct k} : Z * Z :=
  match k with
  | O => (0%Z, 2%Z)
  | S k' =>
     match k' with
     | O => (1%Z, X)
     | S k'' =>
        let L' := Lucas_naive X Y k' p in
          let L'' := Lucas_naive X Y k'' p in
           ( (Z.modulo (Z.sub (Z.mul X  (fst L'))  (Z.mul Y (fst L''))) p),
            (Z.modulo (Z.sub (Z.mul X (snd L')) (Z.mul Y  (snd L''))) p))
     end
  end. 


(*B.1.4 *)
(* p is the size of the prime field, g is the base,
*  X_list is list of samples of X *)
Definition square_root (p g : N) : option N :=
  if N.eqb g 0 then Some 0
  else if N.eqb (N.modulo p 4) 3 then 
    let u := N.div p 4 in
      let y := P_power p g (u + 1) in
        let z := P_sq p y in
          if N.eqb z g then Some y else None
  else if N.eqb (N.modulo p 8) 5 then
    let u := (N.div p 8) in
      let z := P_power p g (N.double u + 1) in
        let t := N.modulo z p in
        if N.eqb t 1 then Some (P_power p g (u + 1))
        else if N.eqb t (p - 1) then Some ((g * 2 * (P_power p (g * 4) u)) mod p)
        else None 
  else (* N.eqb (N.modulo p 8) 1 *)  
    let u := N.div p 8 in
      let Y := g in
        TryFunWithList 
        (fun X =>
          let (U, V) := Lucas p X Y (4 * u + 1) in
            if N.eqb (P_sq p V) (4 * Y mod p) then Some (P_div p V 2)
            else if (andb (N.eqb (U mod p) 1) (N.eqb (U mod p) (p - 1))) then None
            else None 
        )
        (Nlist p) (* Should provide a random sequence *). 

(* A.5.2 *)
Definition recover_p (p a b xp : N)(y_tide : bool) : option (N * N) :=
  let alpha := (xp * xp * xp + a * xp + b) mod p in
    let beta := square_root p alpha in
      match beta with
      | None => None
      | Some beta' =>
          if Bool.eqb (odd beta') y_tide then Some (xp, beta')
          else Some (xp, (p - beta'))
      end.

(* B.1.5 *)
Fixpoint Trace_p_tail (sq_add : N -> N)(T' : N)(j : nat) : N :=
  match j with
  | O => T'
  | S j' =>
      Trace_p_tail sq_add (sq_add T') j'  
  end. 

Definition Trace_p (m gp : N)(alpha : N) : N :=
  let (T, j) := (alpha, N.to_nat (m - 1)) in
    Trace_p_tail (fun x => B_add (Bp_sq gp x) alpha) T j. 

Fixpoint Semi_Trace_p_tail (quad_add : N -> N)(T' : N)(j : nat) : N :=
  match j with
  | O => T'
  | S j' =>
      Semi_Trace_p_tail quad_add (quad_add T') j'
  end. 

Definition Semi_Trace_p (m gp : N)(alpha : N) : N :=
  let (T, j) := (alpha, N.to_nat((m - 1) / 2)) in
    Semi_Trace_p_tail (fun x => B_add (Bp_sq gp (Bp_sq gp x)) alpha) T j. 

(* Find the smallest element in F_2m whose trace is 1*)
Definition SolveTrace1_bfp(m gp : N) : option N :=
  TryBinaryLen (fun x => Trace_p m gp x =? 1) (N.to_nat m). 

Definition FindRoot_alg3 (ml : N -> N -> N)(sq : N -> N)(m beta tau : N) : option N :=
  let (z, w) := 
    (* j is m - i, from m - 1 down to 0, returns (z_i, w_i) *)
    (fix c_loop (j : nat)(z' w' : N) : (N * N) :=
        match j with
        | O => (z', w') (*When i = m, break *)
        | S j' =>
            let z_i := B_add (sq z') (ml (sq w') tau) in
            let w_i := B_add (sq w') beta in
              (z_i, w_i)
        end
    ) (N.to_nat (m - 1)) 0 beta in
  if w =? 0 then None else Some z. 

(*B.1.6*)
(*Find a root of z^2 + z = beta*)
Definition FindRoot_bfp (m gp beta : N) : option N := 
  if beta =? 0 then Some 0 else
  if odd m then
    let z := Semi_Trace_p m gp beta in
    let gamma := B_add (Bp_sq gp beta) z in
      if gamma =? beta then Some z else None
  else
    match SolveTrace1_bfp m gp with
    (*This should not happen since half of F_2m has trace 1*)
    (*As mentioned in B.1.5*)
    | None => None 
    | Some tau => FindRoot_alg3 (Bp_mul gp) (Bp_sq gp) m beta tau
    end. 


(* A.5.3 *)
Definition recover_b (m gp a b xp : N)(yp_tide : bool) : option (N * N):=
  if xp =? 0 then Some (xp, (Bp_power m gp b (N.shiftl 1 (m - 1)))) else
  let beta := B_add (B_add xp a) (Bp_mul gp b (Bp_sq gp (Bp_inv m gp xp))) in
  match FindRoot_bfp m gp beta with
  | None => None
  | Some z => 
     let z_tide := N.odd z in
     (* b.4 compares yp !=? z_tide, which I think is a typo *)
     let yp := Bp_mul gp xp (if (Bool.eqb yp_tide z_tide) then z else z + 1) in
      Some (xp, yp)
  end. 





(*A.5.3*)

(*
Fixpoint neg_bL_tail (bl : bL)(acc : bL) : bL :=
  match bl with
  | h :: tl =>
      neg_bL_tail tl (List.app acc [negb h])
  | [] => acc
  end. 

Definition neg_bl (bl : bL) : bL :=
  neg_bL_tail bl  []. 

Definition inv_m (bl : bL) :=
  neg_bl bl. 

Fixpoint mul_m_tail (x : bL)(y : bL)(acc : bL) : bL :=
  match x, y with
  | hx :: tlx, hy :: tly =>
      mul_m_tail tlx tly (List.app acc [andb hx hy])
  | _, _ => acc
  end.
    
Definition mul_m (x : bL)(y : bL) : bL :=
  mul_m_tail x y []. 

Definition tide_m (xp : bL)(yp : bL) : bool :=
  List.last (mul_m yp (inv_m xp)) false. 
*)

(*4.2.8 prime field case only*)
Inductive cmp_type : Set := 
  cmp : cmp_type | ucp : cmp_type | mix : cmp_type. 


Open Scope list_scope. 
Definition Point2BL (f2Bl : N -> BL)(cp : cmp_type)(xp : N)(yp : N) : BL :=
  let X1 := f2Bl xp in (* a *)
  match cp with
  | cmp => (* b *)
      let yp_tide := tide_p yp in
      match yp_tide with
      | false => x02 :: X1
      | true => x03 :: X1
      end
  | ucp => (* c *)
      x04 :: (X1 ++ (f2Bl yp))
  | mix => (* d *)
      match tide_p yp with
      | false => (x06 :: X1) ++ (f2Bl yp)
      | true => (x07 :: X1) ++ (f2Bl yp)
      end
  end. 

Definition Point2BL_p := Point2BL Field2BL_p.  

Definition Point2BL_b (m : N) := Point2BL (Field2BL_b m).  

(*4.2.9*)
Definition BL2PointStep1 (rcv : N -> bool -> option (N * N))(cp : cmp_type)(q : N)(S : BL) : option (N * N) :=
  match cp with
  | cmp => 
      match S with
      | [] => None
      | PC :: X1 =>
          let xp := BLtoN X1 in
            match PC with
            | x02 => (rcv xp false)
            | x03 => (rcv xp true) 
            | _ => None
            end
      end
  | ucp =>
      match S with
      | [] => None
      | PC :: X1Y1 =>
          let (X1, Y1) := partList X1Y1 (Nat.div (List.length X1Y1)  2%nat) in
            match PC with
            | x04 => Some (BLtoN X1, BLtoN Y1)
            | _ => None
            end
      end
  | mix =>
      match S with
      | [] => None
      | PC :: X1Y1 =>
          let (X1, Y1) := partList X1Y1 (Nat.div (List.length X1Y1)  2%nat) in
          let sampleList := Nlist q in
            let xp := BLtoN X1 in
              match PC with (* I choose e.2.2 TODO how to choose? *)
              | x06 => (rcv xp false)
              | x07 => (rcv xp true) 
              | _ => None
              end
      end
  end. 


Definition BL2PointStep2 (OnCrv : N -> N -> bool)(point : N * N) : option (N * N) :=
  let (xp, yp) := point in
    (*if N.eqb (P_sq p yp) (((P_power p xp 3) + a * xp + b) mod p) then Some point*)
    if OnCrv xp yp then Some point
    else None. 

(*TODO square_root uses Nlist and thus crashes the memory *)
Definition BL2Point_p (cp : cmp_type)(p : N)(a : N)(b : N)(S : BL) : option (N * N) :=
  match BL2PointStep1 (recover_p p a b) cp p S with
  | None => None
  | Some point => BL2PointStep2 (OnCurve_pf p a b) point 
  end. 

Definition BL2Point_bfp (cp : cmp_type)(m gp a b : N)(S : BL) : option (N * N) :=
  match BL2PointStep1 (recover_b m gp a b) cp (N.shiftl 1 m) S with
  | None => None
  | Some point => BL2PointStep2 (OnCurve_bfp gp a b) point
  end. 

(* B.2.1 *)
(* Using Binary GCD instead of Euclidean Alg, just as Pos.gcd does *)
Open Scope positive_scope. 
Fixpoint B_gcd_rcur (a b : positive)(n : nat) : positive :=
  match n with
    | O => 1
    | S n' =>
      match a,b with
        | 1, _ => 1
        | _, 1 => 1
        | a'~0, b'~0 => (B_gcd_rcur a' b' n')~0
        | _ , b'~0 => B_gcd_rcur a b' n'
        | a'~0, _ => B_gcd_rcur a' b n'
        | a'~1, b'~1 =>
          match Pos.lxor a' b' with
            | N0 => b
            | pos r => B_gcd_rcur r (if a' <? b' then a else b) n'
          end
      end
  end.
Definition B_gcd_pos (a b : positive) := B_gcd_rcur a b (Pos.size_nat a + Pos.size_nat b)%nat.

Definition B_gcd (a b : N) : N :=
  match a, b with
  | N0, _ => b
  | _, N0 => a
  | pos a', pos b' => pos (B_gcd_pos a' b')
  end. 

(*
Compute B_gcd 2 0. 
Compute B_gcd 0 3. 
Compute B_gcd 0 0. 
Compute B_gcd 9 5. 
Compute B_gcd 5 9. 
Compute B_gcd 3 5. 
*)

