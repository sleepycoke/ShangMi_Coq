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

Definition T (A : N) : N := L (Tau A). 
Definition T' (A : N) : N := L' (Tau A). 

Definition F (A : N) (B : N) (C : N) (D : N) (E : N) : N :=
  A $ (T (B $ C $ D $ E)). 

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

Definition List4toN (l : list N) : N :=
  (shiftl (hd 0 l) (word_size * 3)) \/
  (shiftl (nth 1 l 0) (word_size * 2)) \/
  (shiftl (nth 2 l 0) word_size) \/
  (nth 3 l 0). 

Definition SM4_enc (i : nat)(x : N) (rk : nat->N) : N :=
  List4toN (firstn 4 (X_list i i (X_list_init x) rk)). 

Definition SM4_dec (i : nat)(y : N)(rk : nat -> N) : N :=
  SM4_enc i y (fun (j : nat) => rk(Nat.sub 31 j)). 

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

Definition rk_ext (MK : N) (i : nat) : N := hd 0 (K_list (i + 1) MK). 

Definition plain := HexString.to_N("0x0123456789abcdeffedcba9876543210"%string).
Definition key := HexString.to_N("0x0123456789abcdeffedcba9876543210"%string).

Definition cyphertext:= HexString.of_N (SM4_enc 32 plain (rk_ext  key)).  
Definition decypheredtext := HexString.of_N (SM4_dec 32 (HexString.to_N cyphertext) (rk_ext key)). 
Definition expCypherText := "0x681edf34d206965e86b3e94f536e4246"%string. 
Compute cyphertext. 
Compute decypheredtext. 

Example self_test : expCypherText = cyphertext.
Proof. reflexivity. Qed. 

