Require Import SMlib.           
Require Import Coq.Lists.List.
Import ListNotations.

Definition Tau (A : N) : N :=
  (Sbox ((land A (255 <<< 24)) >>> 24)) <<< 24 +
  (Sbox ((land A (255 <<< 16)) >>> 16)) <<< 16 +
  (Sbox ((land A (255 <<< 8)) >>> 8)) <<< 8 +
  (Sbox (land A 255)). 

Definition L (B : N) : N :=
  B $ B <<< 2 $ B <<< 10 $ B <<< 18 $ B <<< 24. 
Definition L' (B : N) : N :=
  B $ B <<< 13 $ B <<< 23. 

(* A is 4*32 bit *)
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

Definition X_list_init (x : N) : list N :=
  [(shiftr x (word_size * 0)) /\ mask_ws;
  (shiftr x (word_size * 1)) /\ mask_ws;
  (shiftr x (word_size * 2)) /\ mask_ws;
  (shiftr x (word_size * 3)) /\ mask_ws].


Definition X_list_aux (i : nat)(acc : list N)(rk : nat -> N) : list N :=
  (F (List.nth 3 acc 0) (List.nth 2 acc 0) (List.nth 1 acc 0) (List.nth 0 acc 0) (rk i)) :: acc. 
Fixpoint X_list (i : nat)(init : nat)(acc : list N)(rk : nat -> N) :=
  match i with
  | O => acc
  | S i' => X_list i' init (X_list_aux (init - i)%nat acc rk) rk
  end.

Definition SM4_enc (i : nat)(x : N) (rk : nat->N) : N :=
  R (quad2N (X_vec i (N2quad x) rk)). 

Definition List4toN (l : list N) : N :=
  (shiftl (hd 0 l) (word_size * 3)) \/
  (shiftl (nth 1 l 0) (word_size * 2)) \/
  (shiftl (nth 2 l 0) word_size) \/
  (nth 3 l 0). 

Compute HexString.of_N (List4toN [1;2;3;4]). 
Compute HexString.of_N (List4toN (X_list_init (List4toN [1;2;3;4]))). 

Definition SM4_enc_list (i : nat)(x : N) (rk : nat->N) : N :=
  List4toN (firstn 4 (X_list i i (X_list_init x) rk)). 

Definition SM4_dec (i : nat)(y : N)(rk : nat -> N) : N :=
  SM4_enc i y (fun (j : nat) => rk(Nat.sub 31 j)). 

Definition SM4_dec_list (i : nat)(y : N)(rk : nat -> N) : N :=
  SM4_enc_list i y (fun (j : nat) => rk(Nat.sub 31 j)). 

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

Definition K_list_init (MK : N) : list N :=
  [(mask_44 MK) $ (FK 3); (mask_34 MK) $ (FK 2);
  (mask_24 MK) $ (FK 1); (mask_14 MK) $ (FK 0)]. 

Definition K_list_aux (i : nat)(acc : list N) : list N :=
  (nth 3 acc 0) $ (T' ((nth 2 acc 0) $ (nth 1 acc 0) 
  $ (nth 0 acc 0) $ (CK (of_nat i))) ) :: acc. 

Fixpoint K_list_rec (i : nat)(init : nat)(acc : list N) : list N :=
  match i with
  | O => acc
  | S i' => K_list_rec i' init (K_list_aux (init - i) acc)
  end.

Definition K_list (i : nat)(MK : N) := 
  K_list_rec i i (K_list_init MK). 

Definition rk_ext (MK : N) (i : nat) : N := q4th (K_vec (i + 1) MK). 
Definition rk_ext_bylist (MK : N) (i : nat) : N := hd 0 (K_list (i + 1) MK). 

Definition plain := to_N("0x0123456789abcdeffedcba9876543210"%string).
Definition key := to_N("0x0123456789abcdeffedcba9876543210"%string).
(*
Compute map HexString.of_N (rk_ext_list plain 0 ). 
Compute HexString.of_N (q3rd (K_vec 0 plain)). 
Compute HexString.of_N (q4th (K_vec 0 plain)). 
Compute HexString.of_N (rk_ext plain 0). 
Compute map HexString.of_N (K_list_aux 0 (K_list_init plain)). 


Compute X_list_init plain. 
Compute HexString.of_N (hd 0 (X_list 0 0 (X_list_init plain) (rk_ext key))). 
Compute HexString.of_N (hd 0 (X_list 1 0 (X_list_init plain) (rk_ext key))). 
Compute (map HexString.of_N (X_list 32 31 (X_list_init plain) (rk_ext key))). 
*)
Definition cyphertext := of_N (SM4_enc 32 plain (rk_ext key)).  
Definition cyphertext_bylist:= of_N (SM4_enc_list 32 plain (rk_ext_bylist  key)).  
Definition decypheredtext := of_N (SM4_dec 32 (to_N cyphertext) (rk_ext key)). 
Definition decypheredtext_bylist := of_N (SM4_dec 32 (to_N cyphertext_bylist) (rk_ext_bylist key)). 
Definition expCypherText := "0x681edf34d206965e86b3e94f536e4246"%string. 
Compute cyphertext. 
Compute cyphertext_bylist. 
Compute decypheredtext. 
Compute decypheredtext_bylist. 


Example self_test : expCypherText = cyphertext.
Proof. reflexivity. Qed. 

