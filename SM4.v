Require Import Coq.PArith.BinPosDef. 
Require Import Coq.Strings.BinaryString. 
Require Import Coq.Strings.HexString. 
Require Import Ascii String. 
Require Import Coq.Strings.Ascii. 
Require Import Coq.Strings.String. 
Require Import Tables. 
Require Import NArith.
Require Import CCompLib.Integers.

Locate Integers. 

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
Compute of_N(7 <<< 2). 
Compute of_N(to_N("0xc0000000") <<< 2). 
Compute of_N(to_N("0xc0000000") <<< 1). 
Compute of_N(to_N("0xc0000000") <<< 1 <<< 1). 

Compute lxor 5 7. 

Infix "$" := lxor (at level 50). 
  
Definition quadruple {X : Type} : Type := X * X * X * X. 

Definition q1st {X : Type} (v : quadruple) : X :=
  match v with
  | (x, _, _, _) => x
  end.

Definition q2nd {X : Type} (v : quadruple) : X :=
  match v with
  | (_, x, _, _) => x
  end.
Definition q3rd {X : Type} (v : quadruple) : X :=
  match v with
  | (_, _, x, _) => x
  end.

Definition q4th {X : Type} (v : quadruple) : X :=
  match v with
  | (_, _, _, x) => x
  end.

Check @quadruple N. 

Compute q1st (1, 2, 3, 4). 
Compute q2nd (1, 2, 3, 4). 
Compute q3rd (1%N, 2%N, 3%N, 4%N). 
Compute @q4th N (1%N, 2%N, 3%N, 4%N). 


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
Compute of_N(Tau (to_N("0x55667788"%string))). 
Compute of_N(Tau (to_N("0xfffeeeef"%string))). 

Definition L (B : N) : N :=
  B $ (B <<< 2) $ (B <<< 10) $ (B <<< 18) $ (B <<< 24). 
Definition L' (B : N) : N :=
  (B $ (B <<< 13)) $ (B <<< 23). 

Compute BinaryString.of_N (L' 1). 

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
Compute of_N(mask_14 (to_N("0x11112222333344445555666677778888"%string))). 
Compute of_N(mask_24 (to_N("0x11112222333344445555666677778888"%string))). 
Compute of_N(mask_34 (to_N("0x11112222333344445555666677778888"%string))). 
Compute of_N(mask_44 (to_N("0x11112222333344445555666677778888"%string))). 

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

Compute (O, O). 

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
(* Even more slower since ti calls fb_vec 3 times now. 
Fixpoint fb_vec (i : nat) : prod N N :=
  match i with
  | O => (1%N, 0%N)
  | S i' => ( (add (fst (fb_vec i')) (snd (fb_vec i'))), (fst (fb_vec i'))  )
  end.
*)

Definition fb_axl (vec : prod N N) : prod N N :=
    ( (add (fst vec) (snd vec)), (fst vec)  ). 

Fixpoint fb_vec (i : nat) : prod N N :=
  match i with
  | O => (1%N, 0%N)
  | S i' => fb_axl (fb_vec i')
  end. 

Definition fb_fast (i : nat) : N := snd (fb_vec i). 

Compute fb_fast 40. (* Blazingly fast! *)
Compute fb_fast 600. (* Blazingly fast! *)
Compute sub (fb 30) (fb_fast 30). (* = 0 *)

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
                F (X (i'''') X0 X1 X2 X3 rk) (X (i''') X0 X1 X2 X3 rk)
                  (X (i'') X0 X1 X2 X3 rk) (X (i') X0 X1 X2 X3 rk) (rk i'''')
              end
          end
      end
  end.

Definition X_vec_axl (vec : @quadruple N) (i : nat) (rk : nat -> N) : @quadruple N :=
      (
         q2nd vec, 
         q3rd vec, 
         q4th vec,
         F (q1st vec) (q2nd vec) 
         (q3rd vec) (q4th vec) (rk (i - 1))
      ).

(* X_vec i = (X i, X (i + 1), X (i + 2), X (i + 3)) *)
Fixpoint X_vec (i : nat)(X_vec0 : @quadruple N)(rk : nat -> N) : @quadruple N :=
  match i with
  | O => X_vec0
  | S i' => X_vec_axl (X_vec i' X_vec0 rk) i rk 
  end. 

Definition calXip3 (i : nat)(X0 : N)(X1 : N)(X2 : N)(X3 : N)(rk : nat->N) : N := 
  (shiftl (X (i + 3) X0 X1 X2 X3 rk) (word_size * 3)) +   
  (shiftl (X (i + 2) X0 X1 X2 X3 rk) (word_size * 2)) +   
  (shiftl (X (i + 1) X0 X1 X2 X3 rk) word_size ) +   
  (X i X0 X1 X2 X3 rk). 
Definition SM4_enc (i : nat)(x : N) (rk : nat->N) : N :=
  calXip3 i (mask_14 x) (mask_24 x) (mask_34 x) (mask_44 x) rk. 

Definition quad2N (q : @quadruple N) : N :=
  (shiftl (q1st q) (word_size * 3)) + 
  (shiftl (q2nd q) (word_size * 2)) + 
  (shiftl (q3rd q) (word_size * 1)) + 
  (q4th q). 

Definition N2quad (x : N) : quadruple := 
  ((mask_14 x), (mask_24 x), (mask_34 x), (mask_44 x)). 

Definition quadN2quadX (q : quadruple) : quadruple :=
  (of_N (q1st q), of_N (q2nd q), of_N (q3rd q), of_N (q4th q)). 


Definition SM4_enc_fast (i : nat)(x : N) (rk : nat->N) : N :=
  R (quad2N (X_vec i (N2quad x) rk)). 

Definition SM4_dec (i : nat)(y : N)(rk : nat -> N) : N :=
  SM4_enc i y (fun (i : nat) => rk(31 - i)). 
  
Definition SM4_dec_fast (i : nat)(y : N)(rk : nat -> N) : N :=
  SM4_enc_fast i y (fun (i : nat) => rk(31 - i)). 

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

Definition K_vec_aul (vec : @quadruple N)(i : nat) : @quadruple N :=
  ( (q2nd vec), (q3rd vec), (q4th vec), 
    (q1st vec) $ (T' ( (q2nd vec) $ (q3rd vec) $ (q4th vec) $ (CK (of_nat i) ) )) ). 

(* K_vec i = ( (K 0), (K 1), (K 2), (K 3) ) *)
Fixpoint K_vec (i : nat) (MK : N) : @quadruple N :=
  match i with
  | O => ( (mask_14 MK) $ (FK 0), (mask_24 MK) $ (FK 1),
      (mask_34 MK) $ (FK 2), (mask_44 MK) $ (FK 3) )
  | S i' => K_vec_aul (K_vec i' MK) i'
  end. 


Definition rk_ext  (MK : N) (i : nat): N := K (i + 4) MK. 
Definition rk_ext_fast  (MK : N) (i : nat): N := q4th (K_vec (i + 1) MK). 

Definition plain := to_N("0x0123456789abcdeffedcba9876543210"%string).
Definition key := to_N("0x0123456789abcdeffedcba9876543210"%string).

Compute of_N(K 0 key). 
Compute of_N(K 1 key). 
Compute of_N(K 2 key). 
Compute of_N(K 3 key). 
Compute of_N(K 4 key). 
Compute of_N(K 5 key). (* differ from here *) 
Compute of_N(K 0 0%N). 
Compute of_N(K 1 0%N).
Compute of_N(K 2 0%N).
Compute of_N(K 3 0%N).
Compute of_N(K 4 0%N). (* differ from here *) 

Definition tmp := FK 1 $ FK 2 $ FK 3 $ CK 0. 
Compute of_N(tmp). 
Definition buf := Tau tmp. 
Compute of_N(buf). 
Compute BinaryString.of_N(buf). 
Compute BinaryString.of_N(to_N("0x96690e8a")). 
Compute of_N(buf <<< 13). 
Compute of_N(buf <<< 23). 
Compute of_N(L' (Tau tmp)). 
Compute of_N(T' tmp). 

Compute of_N(rk_ext key 0). 
Compute of_N(rk_ext_fast key 0). 
Compute of_N(rk_ext key 1). 
Compute of_N(rk_ext_fast key 1). 
Compute of_N(rk_ext key 2). 
Compute of_N(rk_ext_fast key 2). 
Compute of_N(rk_ext_fast key 31). 

Definition keyQuad := N2quad key. 
Compute of_N (X 4 (q1st keyQuad) (q2nd keyQuad) (q3rd keyQuad) (q4th keyQuad) (rk_ext_fast key)). 
Compute of_N (X 7 (q1st keyQuad) (q2nd keyQuad) (q3rd keyQuad) (q4th keyQuad) (rk_ext_fast key)). 
Compute quadN2quadX (X_vec 1 (N2quad key) (rk_ext_fast key)). 

Check SM4_enc 32 plain (rk_ext key).  
Check SM4_enc_fast 0 plain (rk_ext_fast key).  
(* Runs forever *)
(*Compute SM4_enc plain (rk_ext key).  *)
Compute of_N (SM4_enc 1 plain (rk_ext_fast key)).  
Compute of_N (SM4_enc_fast 1 plain (rk_ext_fast key)).  
Definition cyphertext := of_N (SM4_enc_fast 32 plain (rk_ext_fast key)).  
Definition decypheredtext := of_N (SM4_dec_fast 32 (to_N cyphertext) (rk_ext_fast key)). 
Compute cyphertext. 
Compute decypheredtext. 
