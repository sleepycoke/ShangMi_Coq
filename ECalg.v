Require Export SM2_DataType. 
  
(*A.5.2*)
Definition tide_p (yp : N) : bool :=
  N.odd yp. 
Print N. 
Print positive.
Compute (xI (xI (xO xH))). (*1011*) 
(*B.1.1*)
Fixpoint power_tail (g : N)(e : bL)(q : N)(acc : N) : N :=
  match e with
  | [] => acc
  | h :: tl =>
      power_tail g tl q 
      match h with
      | true => (N.mul (N.square acc) g) mod q
      | false => (N.square acc) mod q
      end
  end.
Definition power (g : N)(a : N)(q : N) : N :=
  let e := N.modulo a (q - 1) in
  power_tail g (N2bL e) q 1. 

Definition inv_p (g : N)(q : N) : N :=
  power g (q - 2) q. 

(*TODO rename *)
Definition F_inv (g q : N) :=
  inv_p g q. 

Definition F_add (x y q : N) :=
  (x + y) mod q. 

Definition F_mul (x y q : N) :=
  (x * y) mod q. 

Definition F_sub (x y q : N) :=
  (q + x - y) mod q.

Definition F_div (x : N)(y : N)(q : N) : N :=
  (N.mul x (inv_p y q)) mod q. 

Compute inv_p 7 11. 
Compute F_div 7 2 11. 

Compute power 3 5 5. 
Compute power 0 1 5. 
(*B.1.3*)
Fixpoint Lucas_tail (X : N)(Delta : N)(k : bL)(p : N)(acc : N * N) : N * N :=
  match k with
  | [] => acc
  | ki :: tl =>
      match acc with (U0, V0) =>
        let (U1, V1) := 
            ((U0 * V0) mod p, (F_div ((N.square V0) + Delta * (N.square U0))) 2 p) in
          match ki with
          | false => Lucas_tail X Delta tl p (U1, V1)
          | true => Lucas_tail X Delta tl p 
              ((F_div (X * U1 + V1) 2 p), (F_div (X * V1 + Delta * U1) 2 p)) 
          end
      end
  end.

Compute N2bL 0. 

(* X, Y > 0 *)
Definition Lucas (X : N)(Y : N)(k : N)(p : N) :=
  match N2bL k with
  | true :: k' => (* k > 0 *)
    Lucas_tail X (((N.square X) + 4 * (p - Y)) mod p) k' p (1, X)
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

Compute Lucas 3 2 0 7.  
Compute Lucas_naive 3 2 0 7. 
Compute Lucas 3 2 1 7.  
Compute Lucas_naive 3 2 1 7. 
Compute Lucas 3 2 2 7.  
Compute Lucas_naive 3 2 2 7. 
Compute Lucas 5 2 15 7.  
Compute Lucas_naive 5 2 15 7. 
Compute Lucas 2 6 2 7.
Compute Lucas_naive 2 6 2 7. 
Compute Lucas 2 6 1 7.  
Compute Lucas_naive 2 6 1 7. 
Compute (((N.square 2) + 4 * (7 - 6)) mod 7). 
Compute Z.modulo (-1) 7. 

(* Try each element x in l with func : option N. 
* If func x is not None then return its value otherwise keep trying. 
* If all None then return None. *)
Fixpoint TryFunWithList (l : list N)(func : N -> option N) : option N :=
  match l with
  | [] => None
  | x :: tl =>
      match func x with
      | Some y => Some y
      | None => TryFunWithList tl func
      end
  end. 

Fixpoint Nlist_tail (k : nat)(acc : list N) : list N :=
  match k with
  | O => acc
  | S k' =>
      Nlist_tail k' ((N.of_nat k') :: acc)
  end.

(*Generates [0; 1; 2; ... ; len - 1]*)
Definition Nlist (len : N) : list N :=
  Nlist_tail (N.to_nat len) []. 

Compute Nlist 3. 


(*B.1.4*)

Definition square_root (g : N)(p : N) : option N :=
  if N.eqb g 0 then Some 0
  else if N.eqb (N.modulo p 4) 3 then 
    let u := N.div p 4 in
      let y := power g (u + 1) p in
        let z := N.modulo (N.square y) p in
          if N.eqb z g then Some y else None
  else if N.eqb (N.modulo p 8) 5 then
    let u := (N.div p 8) in
      let z := power g (N.double u + 1) p in
        let t := N.modulo z p in
        if N.eqb t 1 then Some (power g (u + 1) p)
        else if N.eqb t (p - 1) then Some ((g * 2 * (power (g * 4) u p)) mod p)
        else None 
  else (* N.eqb (N.modulo p 8) 1 *)  
    let u := N.div p 8 in
      let Y := g in
        TryFunWithList (Nlist p) (* Should provide a random sequence *)
        (fun X =>
          let (U, V) := Lucas X Y (4 * u + 1) p in
            if N.eqb ((N.square V) mod p) (4 * Y mod p) then Some (V / 2 mod p)
            else if (andb (N.eqb (U mod p) 1) (N.eqb (U mod p) (p - 1))) then None
            else None 
        ). 
      

Compute square_root 0 5. 
Compute square_root 2 13. 
Compute square_root 4 5. 
Compute square_root 12 13. 


Definition recover_p (p : N)(a : N)(b : N)(xp : N)(y_tide : bool) : option (N * N) :=
  let alpha := (xp * xp * xp + a * xp + b) mod p in
    let beta := square_root alpha p in
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

Compute neg_bl [true; false; true; true]. 
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

Compute mul_m [true; true; false; false] [false; true; true; false]. 

Print List.last. 

Definition tide_m (xp : bL)(yp : bL) : bool :=
  List.last (mul_m yp (inv_m xp)) false. 
*)

(*4.2.8 prime field case only*)
Inductive cmp_type : Set := 
  cmp : cmp_type | ucp : cmp_type | mix : cmp_type. 


Open Scope list_scope. 
Definition Point2BL_p (xp : N)(yp : N)(cp : cmp_type) : BL :=
  let X1 := Field2BL_p xp in (* a *)
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

Compute partList [1;2;3;4] 2. 

(*4.2.9 still only prime field case*)
Definition BL2PointStep1_p (p : N)(a : N)(b : N)(S : BL)(cp : cmp_type) : option (N * N) :=
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
    if N.eqb ((N.square yp) mod p) (((power xp 3 p) + a * xp + b) mod p) then Some point
    else None. 

Definition BL2Point_p (p : N)(a : N)(b : N)(S : BL)(cp : cmp_type) : option (N * N) :=
  match BL2PointStep1_p p a b S cp with
  | None => None
  | Some point => BL2PointStep2_p p a b point
  end. 

            

  
  




