Require Import SMlib.



(* ByteList is indeed a list of bytes*)
Definition BL := list byte. 
(* BitList is indeed a list of bool*)
Definition bL := list bool. 

Fixpoint BL2N_tail (bl : BL)(acc : N) : N :=
  match bl with
  | [] => acc
  | h :: tl =>
      BL2N_tail tl (acc * 256 + (Byte.to_N h)) 
  end.

Compute BL2N_tail [x01; x02] 0. 

(*4.2.2*)
Fixpoint BL2N (bl : BL) : N :=
  BL2N_tail bl 0.

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
      N2BL_tail (N.div x 256) k'(N2Byte (N.modulo x 256) :: acc)
  end.

Compute N2BL_tail 1025 3 []. 

(*4.2.1*)
Definition N2BL (x : N)(k : nat) : BL :=
  N2BL_tail x k [].

Compute N2BL 1025 4.

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

Definition bL2N (bl : bL)(k : nat) :=
  bL2N_tail bl k 0.

Compute bL2N [true;true;true] 4. 
Compute bL2N [true;true;true] 3. 
Compute bL2N [true;true;true] 2. 

(* tranfrom the first k bits into a byte *)
Definition bL2Byte (bl : bL)(k : nat) :=
  N2Byte (bL2N bl k). 

Compute bL2Byte [true;true;true] 4. 

Print list. 

(* returns the prefix of length k * the rest *)
Fixpoint subList_tail (A : Type)(l : list A)(len : nat)(acc : list A * list A) : list A * list A :=
  match len with
  | O => acc
  | S len' =>
      match l with
      | [] => acc
      | h :: tl =>
          subList_tail A tl len' ((List.app (fst acc) [h]), List.tl (snd acc))
      end
  end.

Definition subList {A} (l : list A)(len : nat) :=
  subList_tail A l len ([], l). 

Compute subList [1;2;3] 0. 
Compute subList [1;2;3] 3. 
Compute subList [1;2;3] 4. 

Definition subListBack {A} (l : list A)(backLen : nat) :=
  subList l ((List.length l) - backLen).

Compute subListBack [1;2;3] 4. 
Compute subListBack [1;2;3] 2. 

(*4.2.3*)
Fixpoint bL2BL_tail (s : bL)(k : nat)(acc : BL) : BL :=
  match k with
  | O => acc 
  | S k' =>
      (fun sl => bL2BL_tail (fst sl) k' 
      (List.app [bL2Byte (snd sl) 8] acc)) (subListBack s 8)
  end.


Definition bL2BL (s : bL) : BL :=
  bL2BL_tail s (Nat.div (Nat.add(List.length s) 7%nat) 8%nat) []. 

Compute bL2BL [true;true;true;false; true;true;true;true; true;true;true;true; true;true;true;true; true;true;false;true].  

Compute bL2BL [true;true;true;true;true;true;true;true;false;true]. 
