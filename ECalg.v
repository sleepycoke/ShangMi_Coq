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
  match N2bL k with
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

(* Try each element x in l with func : option N. 
* If func x is not None then return its value otherwise keep trying. 
* If all None then return None. *)
Fixpoint TryFunWithList (func : N -> option N)(l : list N) : option N :=
  match l with
  | [] => None
  | x :: tl =>
      match func x with
      | Some y => Some y
      | None => TryFunWithList func tl 
      end
  end. 

(*B.1.4*)
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
    
Definition recover_p (p a b xp : N)(y_tide : bool) : option (N * N) :=
  let alpha := (xp * xp * xp + a * xp + b) mod p in
    let beta := square_root p alpha in
      match beta with
      | None => None
      | Some beta' =>
          if Bool.eqb (odd beta') y_tide then Some (xp, beta')
          else Some (xp, (p - beta'))
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
      x04 :: (X1 ++ (Field2BL_p yp))
  | mix => (* d *)
      match tide_p yp with
      | false => (x06 :: X1) ++ (Field2BL_p yp)
      | true => (x07 :: X1) ++ (Field2BL_p yp)
      end
  end. 

Definition Point2BL_p := Point2BL Field2BL_p.  

Definition Point2BL_b (m : N) := Point2BL (Field2BL_b m).  

(*4.2.9 still only prime field case*)
Definition BL2PointStep1_p (cp : cmp_type)(p : N)(a : N)(b : N)(S : BL) : option (N * N) :=
  match cp with
  | cmp => 
      match S with
      | [] => None
      | PC :: X1 =>
          let xp := BL2N X1 in
            match PC with
            | x02 => (recover_p p a b xp false)
            | x03 => (recover_p p a b xp true) 
            | _ => None
            end
      end
  | ucp =>
      match S with
      | [] => None
      | PC :: X1Y1 =>
          let (X1, Y1) := partList X1Y1 (Nat.div (List.length X1Y1)  2%nat) in
            match PC with
            | x04 => Some (BL2N X1, BL2N Y1)
            | _ => None
            end
      end
  | mix =>
      match S with
      | [] => None
      | PC :: X1Y1 =>
          let (X1, Y1) := partList X1Y1 (Nat.div (List.length X1Y1)  2%nat) in
          let sampleList := Nlist p in
            let xp := BL2N X1 in
              match PC with (* I choose e.2.2 TODO how to choose? *)
              | x06 => (recover_p p a b xp false)
              | x07 => (recover_p p a b xp true) 
              | _ => None
              end
      end
  end. 

Definition BL2PointStep2_p (p : N)(a : N)(b : N)(point : N * N) : option (N * N) :=
  let (xp, yp) := point in
    if N.eqb (P_sq p yp) (((P_power p xp 3) + a * xp + b) mod p) then Some point
    else None. 

Definition BL2Point_p (cp : cmp_type)(p : N)(a : N)(b : N)(S : BL) : option (N * N) :=
  match BL2PointStep1_p cp p a b S with
  | None => None
  | Some point => BL2PointStep2_p p a b point
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
Close Scope positive_scope.

