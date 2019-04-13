Require Import Coq.PArith.BinPosDef. 
Require Import Coq.Strings.HexString. 
Require Import Ascii String. 
Require Import Coq.Strings.Ascii. 
Require Import Coq.Strings.String. 
Require Import Tables. 
Require Import NArith.

Import N. 
Definition word_size := 32%N. 
Definition modulus := shiftl 1 word_size.
Definition half_modulus := div2 modulus.  

Compute of_N modulus. 
Compute of_N half_modulus. 

Compute Sbox(254).  
Compute Sbox(255).  

Definition shiftr1_cyc (n : N) : N := 
  match n with
  | N0 => N0 
  | Npos p =>
      match p with
      | xH => half_modulus
      | xO p' => Npos p'
      | xI p' => half_modulus + Npos p'
      end
  end.

Compute shiftr1_cyc 0.
Compute shiftr1_cyc 1. 
Compute of_N (shiftr1_cyc 3). 
Compute of_N (shiftr1_cyc 4). 
Compute of_N (shiftr1_cyc 5). 

(* n >>> t*)
Definition shiftr_cyc (n : N) (t : N) : N :=
  N.iter t shiftr1_cyc n . 


Infix ">>>" := shiftr_cyc (at level 35). 


Definition shiftl_cyc (n: N) (t : N) : N :=
  shiftr_cyc n (word_size - t). 

Infix "<<<" := shiftl_cyc (at level 35). 

Compute of_N( 7 >>> 2). 
Compute of_N((7 >>> 2) <<< 2). 

Compute lxor 5 7. 

Infix "$" := lxor (at level 50). 

Compute 5 $ 7. 

Compute land 5 3.

Compute shiftl 2 1. 

Compute (of_N(255 <<< 24)). 

Definition Tau (A : N) : N :=
  (Sbox ((land A (255 <<< 24)) >>> 24)) <<< 24 +
  (Sbox ((land A (255 <<< 16)) >>> 16)) <<< 16 +
  (Sbox ((land A (255 <<< 8)) >>> 8)) <<< 8 +
  (Sbox (land A 255)). 

Compute of_N(Tau (to_N("0x11223344"%string))). 

Definition L (B : N) : N :=
  B $ B <<< 2 $ B <<< 10 $ B <<< 18 $ B <<< 24. 
Definition L' (B : N) : N :=
  B $ B <<< 13 $ B <<< 23. 

Definition mask_ws := sub modulus 1. 
Definition mask_14 (A : N) : N := 
  shiftr (land A (shiftl mask_ws (word_size * 3))) (word_size * 3). 
Definition mask_24 (A : N) : N := 
  shiftr (land A (shiftl mask_ws (word_size * 2))) (word_size * 2). 
Definition mask_34 (A : N) : N := 
  shiftr (land A (shiftl mask_ws (word_size * 1))) (word_size * 1). 
Definition mask_44 (A : N) : N := 
  land A mask_ws. 

Compute of_N(mask_ws). 
  
Definition R (A : N) : N := 
  shiftl (mask_44 A) (word_size * 3) +
  shiftl (mask_34 A) (word_size * 2) +
  shiftl (mask_24 A) (word_size * 1) +
  shiftl (mask_14 A) (word_size * 0).

Compute of_N(R (to_N("0x11112222333344445555666677778888"%string))). 

Definition T (A : N) : N := L (Tau A). 
Definition T' (A : N) : N := L' (Tau A). 

Definition F (A : N) (B : N) (C : N) (D : N) (E : N) : N :=
  A $ (T (B $ C $ D $ E)). 

(* ill-formed 
Fixpoint fb (i : N) :=
  if eqb i 0%N then 0 else
  if eqb i 1%N then 1 else
  (fb (i - 1)) + (fb (i - 2)). 
  *)

Fixpoint fb (i : nat) : N :=
  match i with
  | O => 0
  | S j =>
      match j with
      | O => 1
      | S k => fb k + fb j
      end
  end.

(*Compute fb 40.  Takes 14 secs to compute. fb 60 takes more than 3 mins *)

(* ill-formed
Fixpoint X(i : N)(X0 : N)(X1 : N)(X2 : N)(X3 : N) {struct i} : N :=
  if eqb i 0 then X0 else
  if eqb i 1 then X1 else
  if eqb i 2 then X2 else
  if eqb i 3 then X3 else
  F (X (i - 4) X0 X1 X2 X3) (X (i - 3) X0 X1 X2 X3) (X (i - 2) X0 X1 X2 X3) (X (i - 1) X0 X1 X2 X3) (rk (i - 4)). 
  *)
(* expected i as N
Fixpoint X(i : nat)(X0 : N)(X1 : N)(X2 : N)(X3 : N) {struct i} : N :=
  if eqb i 0 then X0 else
  if eqb i 1 then X1 else
  if eqb i 2 then X2 else
  if eqb i 3 then X3 else
  F (X (i - 4) X0 X1 X2 X3) (X (i - 3) X0 X1 X2 X3) (X (i - 2) X0 X1 X2 X3) (X (i - 1) X0 X1 X2 X3) (rk (i - 4)). 
*)
Fixpoint X(i : nat)(X0 : N)(X1 : N)(X2 : N)(X3 : N)(rk : nat -> N)  {struct i} : N :=
  match i with
  | O => X0
  | S i' =>
      match i' with
      | O => X1
      | S i'' =>
          match i'' with
          | O => X2
          | S i''' => 
              match i''' with
              | O => X3
              | S i'''' =>
  F (X (i'''') X0 X1 X2 X3 rk) (X (i''') X0 X1 X2 X3 rk) (X (i'') X0 X1 X2 X3 rk) (X (i') X0 X1 X2 X3 rk) (rk i'''')
              end
          end
      end
  end.

Definition calX35_32 (X0 : N)(X1 : N)(X2 : N)(X3 : N)(rk : nat->N) : N := 
  (shiftl (X 35 X0 X1 X2 X3 rk) (word_size * 3)) +   
  (shiftl (X 34 X0 X1 X2 X3 rk) (word_size * 2)) +   
  (shiftl (X 33 X0 X1 X2 X3 rk) word_size ) +   
  (X 32 X0 X1 X2 X3 rk). 
  

Definition SMS4_enc (x : N) (rk : nat->N) : N :=
  calX35_32 (mask_14 x) (mask_24 x) (mask_34 x) (mask_44 x) rk. 

Print SMS4_enc. 
Definition SMS4_dec (y : N)(rk : nat -> N) : N :=
  SMS4_enc y (fun (i : nat) => rk(31 - i)). 
  
Fixpoint K (i : nat) (MK : N) : N := 
  match i with
  | O => (mask_14 MK) $ (FK 0)
  | S i' =>
      match i' with
      | O => (mask_24 MK) $ (FK 1)
      | S i'' =>
          match i'' with
          | O => (mask_34 MK) $ (FK 2)
          | S i''' =>
              match i''' with
              | O => (mask_44 MK) $ (FK 3)
              | S i'''' =>
                  (K i'''' MK) $ (T' ((K i''' MK) $ (K i'' MK) $ (K i' MK) $ (CK (of_nat i''''))))
              end
          end
      end
  end.  

Definition rk_ext  (MK : N) (i : nat): N := K (i + 4) MK. 

Definition plain := to_N("0x0123456789abcdeffedcba9876543210"%string).
Definition key := to_N("0x0123456789abcdeffedcba9876543210"%string).
Check SMS4_enc plain (rk_ext key).  
(* Runs forever *)
(*Compute SMS4_enc plain (rk_ext key).  *)
