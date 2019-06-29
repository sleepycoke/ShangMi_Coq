Require Import SMlib.
Require Import Coq.Strings.Ascii.

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

Print byte. 

Compute even 2. 

Fixpoint N2bL_tail (n : N)(k : nat)(acc : bL) : bL :=
  match k with
  | O => acc
  | S k' => 
      N2bL_tail (N.div n 2) k' (N.odd n :: acc)
  end.

Compute N2bL_tail 254 8 []. 

Definition N2bL (n : N) : bL :=
  N2bL_tail n 8 [].

Compute N2bL 127. 


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

(*4.2.5*)
Definition Field2BL_a (alpha : N) :=
  N2BL alpha. 

Definition Field2BL_b (alpha : bL) :=
  bL2BL alpha. 

(*4.2.6*)
Definition BL2Field_a (Bl : BL)(q : N) : option N :=
  (fun (alpha : N)  => if leb q alpha then None else Some alpha) (BL2N Bl).  

Definition BL2Field_b (Bl : BL) : bL :=
  BL2bL Bl. 

Compute BL2Field_a [x07] 7. 
Compute BL2Field_a [x06] 7. 

(*4.2.7*)
Definition Field2N_b (alpha : bL) : N :=
  bL2N alpha. 

(*4.2.8*)



