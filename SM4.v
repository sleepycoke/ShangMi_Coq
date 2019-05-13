Require Import SMlib.           


Definition Tau (A : N) : N :=
  (Sbox ((land A (255 <<< 24)) >>> 24)) <<< 24 +
  (Sbox ((land A (255 <<< 16)) >>> 16)) <<< 16 +
  (Sbox ((land A (255 <<< 8)) >>> 8)) <<< 8 +
  (Sbox (land A 255)). 

Definition L (B : N) : N :=
  B $ B <<< 2 $ B <<< 10 $ B <<< 18 $ B <<< 24. 
Definition L' (B : N) : N :=
  B $ B <<< 13 $ B <<< 23. 
Definition R (A : N) : N := 
  shiftl (mask_44 A) (word_size * 3) +
  shiftl (mask_34 A) (word_size * 2) +
  shiftl (mask_24 A) (word_size * 1) +
  shiftl (mask_14 A) (word_size * 0).

Definition T (A : N) : N := L (Tau A). 
Definition T' (A : N) : N := L' (Tau A). 

Definition F (A : N) (B : N) (C : N) (D : N) (E : N) : N :=
  A $ (T (B $ C $ D $ E)). 
Definition X_vec_aux (vec : @quadruple N) (i : nat) (rk : nat -> N) : @quadruple N :=
      (
         q2nd vec, 
         q3rd vec, 
         q4th vec,
         F (q1st vec) (q2nd vec) 
         (q3rd vec) (q4th vec) (rk i)
      ).

(* X_vec i = (X i, X (i + 1), X (i + 2), X (i + 3)) *)
Fixpoint X_vec (i : nat)(X_vec0 : @quadruple N)(rk : nat -> N) : @quadruple N :=
  match i with
  | O => X_vec0
  | S i' => X_vec_aux (X_vec i' X_vec0 rk) i' rk 
  end. 

Definition SM4_enc (i : nat)(x : N) (rk : nat->N) : N :=
  R (quad2N (X_vec i (N2quad x) rk)). 

Definition SM4_dec (i : nat)(y : N)(rk : nat -> N) : N :=
  SM4_enc i y (fun (j : nat) => rk(Nat.sub 31 j)). 

Definition K_vec_aux (vec : @quadruple N)(i : nat) : @quadruple N :=
  ( (q2nd vec), (q3rd vec), (q4th vec), 
    (q1st vec) $ (T' ( (q2nd vec) $ (q3rd vec) $ (q4th vec) $ (CK (of_nat i) ) )) ). 

(* K_vec i = ( (K 0), (K 1), (K 2), (K 3) ) *)
Fixpoint K_vec (i : nat) (MK : N) : @quadruple N :=
  match i with
  | O => ( (mask_14 MK) $ (FK 0), (mask_24 MK) $ (FK 1),
      (mask_34 MK) $ (FK 2), (mask_44 MK) $ (FK 3) )
  | S i' => K_vec_aux (K_vec i' MK) i'
  end. 

Definition rk_ext (MK : N) (i : nat): N := q4th (K_vec (i + 1) MK). 

Definition plain := to_N("0x0123456789abcdeffedcba9876543210"%string).
Definition key := to_N("0x0123456789abcdeffedcba9876543210"%string).

Definition cyphertext := of_N (SM4_enc 32 plain (rk_ext key)).  
Definition decypheredtext := of_N (SM4_dec 32 (to_N cyphertext) (rk_ext key)). 
Definition expCypherText := "0x681edf34d206965e86b3e94f536e4246"%string. 
Compute cyphertext. 
Compute decypheredtext. 

Example self_test : expCypherText = cyphertext.
Proof. reflexivity. Qed. 

