Require Export SMlib.
Require Export Coq.Strings.Ascii.

Fixpoint RepChar_tail (s : string)(old : ascii)(new acc : string) : string :=
  match s with
  | "" => acc
  | String h t => 
      RepChar_tail t old new (acc ++
        if Ascii.eqb h old then new else (String h "")
      )
  end. 

Definition RepChar (s : string)(old : ascii)(new : string) : string :=
  RepChar_tail s old new "". 

(* ByteList is indeed a list of bytes*)
Definition BL := list byte. 
(* BitList is indeed a list of bool*)
Definition bL := list bool. 
Fixpoint bS2bL_tail (bs : string)(acc : bL) : bL :=
  match bs with
  | EmptyString => acc 
  | String head tl =>
      match ascii_to_digit head with
      | Some 1 => bS2bL_tail tl (List.app acc [true])
      | _ => bS2bL_tail tl (List.app acc [false])
      end
  end.

Definition bS2bL (bs : string) : bL :=
  bS2bL_tail bs []. 

Fixpoint bL2bS_tail (bl : bL)(acc : string) : string :=
  match bl with
  | [] => acc
  | head :: tl =>
      match head with
      | true => bL2bS_tail tl (acc ++ "1")
      | false => bL2bS_tail tl (acc ++ "0")
      end
  end.

Definition bL2bS (bl : bL) : string :=
  bL2bS_tail bl "". 

Compute bL2bS [true;false]. 

Compute bS2bL "11001". 




Fixpoint BL2N_tail (Bl : BL)(acc : N) : N :=
  match Bl with
  | [] => acc
  | h :: tl =>
      BL2N_tail tl (acc * 256 + (Byte.to_N h)) 
  end.

Compute BL2N_tail [x01; x02] 0. 

(*4.2.2*)
Fixpoint BL2N (Bl : BL) : N :=
  BL2N_tail Bl 0.

Compute BL2N [x02; xaa]. 

Definition N2Byte (n : N) : byte :=
  match Byte.of_N n with
  | None => x00
  | Some b => b
  end.

Compute N2Byte 256. 
Compute N2Byte 255. 

Fixpoint N2BL_tail (x : N)(k : nat)(acc : BL) : BL :=
  match k with
  | O => acc
  | S k' => 
      N2BL_tail (N.div x 256) k' (N2Byte (N.modulo x 256) :: acc)
  end.

Compute N2BL_tail 1025 3 []. 
Compute N2BL_tail (256*256 + 1025) 3 []. 
Compute N2BL_tail (2 * 256*256 + 1025) 3 []. 
Compute N2BL_tail (128 * 256*256 + 1025) 3 []. 
Compute N2BL_tail (256 * 256*256 + 1025) 3 []. 

(*4.2.1 trunk from right*)
Definition N2BL_len (x : N)(k : nat) : BL :=
  N2BL_tail x k [].

Compute N2BL_len 1025 4.

Print bool. 

(* Transform the first k(<= 8) bits into an N *)  
Fixpoint bL2N_tail (bl : bL)(k : nat)(acc : N) : N :=
  match k with
  | O => acc
  | S k' => 
      match bl with
      | [] => acc
      | h :: tl => 
          match h with
          | false => bL2N_tail tl k' (N.double acc)
          | true => bL2N_tail tl k' (N.add 1 (N.double acc))
          end
      end
  end.

(*4.2.2*)
Definition bL2N (bl : bL) :=
  bL2N_tail bl (List.length bl) 0.

Compute bL2N [true;true;true] . 

Definition bL2N_prefix (bl :bL)(k : nat) : N :=
  bL2N_tail bl k 0.

Compute bL2N_prefix [true;true;true] 2. 

(* tranfrom the first k bits into a byte *)
Definition bL2Byte (bl : bL)(k : nat) :=
  N2Byte (bL2N_prefix bl k). 

Compute bL2Byte [true;true;true] 4. 

Print list. 

(* returns the prefix of length k * the rest *)
Fixpoint partList_tail (A : Type)(l : list A)(len : nat)(acc : list A * list A) : list A * list A :=
  match len with
  | O => acc
  | S len' =>
      match l with
      | [] => acc
      | h :: tl =>
          partList_tail A tl len' ((List.app (fst acc) [h]), List.tl (snd acc))
      end
  end.

Definition partList {A} (l : list A)(len : nat) :=
  partList_tail A l len ([], l). 

Compute partList [1;2;3] 0. 
Compute partList [1;2;3] 3. 
Compute partList [1;2;3] 4. 

Definition partListBack {A} (l : list A)(backLen : nat) :=
  partList l ((List.length l) - backLen).

Compute partListBack [1;2;3] 4. 
Compute partListBack [1;2;3] 2. 

Fixpoint subList_tail {A} (start : nat)(length : nat)(l : list A)(acc : list A) :=
  match l with
  | [] => acc
  | h :: tl =>
    match start with
    | S start' => subList_tail start' length tl acc
    | O =>
       match length with
       | O => acc
       | S length' =>
          subList_tail start length' tl (acc ++ [h])
       end
    end
  end.  

Definition subList {A} (start : nat)(length : nat)(l : list A) :=
  subList_tail start length l [].

Compute subList 1 2 [1;2;3]. 
Compute subList 0 2 [1;2;3]. 

(*4.2.3*)
Fixpoint bL2BL_tail (s : bL)(k : nat)(acc : BL) : BL :=
  match k with
  | O => acc 
  | S k' =>
      (fun sl => bL2BL_tail (fst sl) k' 
      (List.app [bL2Byte (snd sl) 8] acc)) (partListBack s 8)
  end.


Definition bL2BL (s : bL) : BL :=
  bL2BL_tail s (Nat.div (Nat.add(List.length s) 7%nat) 8%nat) []. 

Compute bL2BL [true;true;true;false; true;true;true;true; true;true;true;true; true;true;true;true; true;true;false;true].  

Compute bL2BL [true;true;true;true;true;true;true;true;false;true]. 

Print byte. 

Compute even 2. 

Fixpoint N2bL_tail (n : N)(k : nat)(acc : bL) : bL :=
  match k with
  | O => acc
  | S k' => 
      N2bL_tail (N.div n 2) k' (N.odd n :: acc)
  end.

Compute N2bL_tail 254 8 []. 

(* [] for 0, trunk from right. *)
Definition N2bL_len (n : N)(len : nat) : bL :=
  N2bL_tail n len []. 

Compute N2bL_len 127 2. 
Compute N2bL_len (1024 + 127) 4. 
Compute N2bL_len 3 4. 

Definition N2bL (n : N) : bL :=
  N2bL_len n (N.to_nat (N.size n)).

Compute N2bL 127. 
Compute N2bL 3. 
Compute N2bL 4. 
Compute N2bL 0. 


(*4.2.4*)
Fixpoint BL2bL_tail (M : BL)(k : nat)(acc : bL) : bL :=
  match k with
  | O => acc
  | S k'=> 
      match M with
      | [] => acc
      | h :: tl =>
          BL2bL_tail tl k' (List.app acc (N2bL (Byte.to_N h)))
      end
  end.

Definition BL2bL (M : BL) : bL :=
  BL2bL_tail M (List.length M) [].

Compute BL2bL [].
Compute BL2bL [xff].
Compute BL2bL [x01; xff].

Definition N2bS (n : N) : string :=
  bL2bS (N2bL n).

Definition N2bS_len (n : N)(len : nat) : string :=
  bL2bS (N2bL_len n len).

Compute N2bS 6. 

Fixpoint hS2bS_tail (m_hex : string)(acc : string) : string :=
  match m_hex with
  | "" => acc
  | String h tl =>
      match HexString.ascii_to_digit h with
      | None => ""
      | Some v => hS2bS_tail tl (acc ++ N2bS_len v 4)
      end
  end. 

Definition hS2bS (m_hex : string) : string :=
  hS2bS_tail m_hex "".

Print HexString.Raw.to_N. 
Definition hS2N (m_hex : string) : N :=
  HexString.Raw.to_N (RepChar m_hex " "%char ""%string) 0. 

Definition N2hS (n : N) : string :=
  match n with
  | Npos p => HexString.Raw.of_pos p ""
  | N0 => ""
  end.  

Fixpoint bL2hS_tail (bl : bL)(hSLen : nat)(acc : string) : string :=
  match hSLen with
  | O => acc
  | S len' =>
  let (pre, suf) := partListBack bl 16 in
    match suf with
    | [] => acc
    | _ => bL2hS_tail pre len' (acc ++ (N2hS (bL2N suf)))
    end
  end.

Definition bS2hS (m_bin : string) : string :=
  let bl := bS2bL m_bin in
    bL2hS_tail bl (Nat.div (Nat.add (String.length m_bin) 15%nat) 16%nat) "".

(*4.2.5*)

Inductive field_type : Set :=
  pri : field_type | ext : field_type .
Definition Field2BL_p (alpha : N) : BL :=
  N2BL_len alpha (N.to_nat (N.div (alpha + 7) 8)). 

Definition Field2BL_m (alpha : bL) :=
  bL2BL alpha. 

(*4.2.6*)
Definition BL2Field_p (Bl : BL)(q : N) : option N :=
  (fun (alpha : N)  => if leb q alpha then None else Some alpha) (BL2N Bl).  

Definition BL2Field_m (Bl : BL) : bL :=
  BL2bL Bl. 

Compute BL2Field_p [x07] 7. 
Compute BL2Field_p [x06] 7. 

(*4.2.7*)
Definition Field2N_m (alpha : bL) : N :=
  bL2N alpha. 

(*A.5.2*)
Definition tide_p (yp : N) : bool :=
  N.odd yp. 
Print N. 
Print positive.
Compute (xI (xI (xO xH))). (*1011*) 
(*B.1.1*)
Fixpoint power_tail (g : N)(e : bL)(acc : N) : N :=
  match e with
  | [] => acc
  | h :: tl =>
      match h with
      | true => power_tail g tl (N.mul (N.square acc) g)
      | false => power_tail g tl (N.square acc)
      end
  end.
Definition power (g : N)(a : N)(q : N) : N :=
  let e := N.modulo a (q - 1) in
  N.modulo (power_tail g (N2bL e) 1) q. 

Definition inv_p (g : N)(q : N) : N :=
  power g (q - 2) q. 

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

Fixpoint neg_bL_tail (bl : bL)(acc : bL) : bL :=
  match bl with
  | h :: tl =>
      neg_bL_tail tl (List.app acc [negb h])
  | [] => acc
  end. 

Definition neg_bl (bl : bL) : bL :=
  neg_bL_tail bl  []. 

Compute neg_bl [true; false; true; true]. 
(*
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

            

  
  




