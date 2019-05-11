Require Import SMlib.
Require Import Coq.ZArith.BinIntDef.  
Require Import Coq.Strings.BinaryString. 
Require Import Program Arith.
Require Import Coq.ZArith.BinIntDef. 

(* The p-th segment of n, of lenth en, divided into q parts 
Definition segment (p : nat) (q : nat) (len : N) (n : N) :=*)

Open Scope N. 

(* https://en.cppreference.com/w/c/language/operator_precedence *)
(* Bit-wise operation are below + -*)
Infix "/\" := land : N_scope.
Infix "\/" := lor : N_scope.
(* ~ n with respect to word_size *)
Definition neg_ws (n : N) : N := 
  n $ mask_ws. 
Notation "~ n" := (neg_ws n) (at level 75, right associativity) : N_scope. 

Definition add_ws (m : N)(n : N) : N := 
  (m + n) /\ mask_ws.  

Infix "+ws" := add_ws (at level 50): N_scope. 

Compute 9 /\ 10. 
Compute of_N (~ 1 + 3). 
Compute of_N (~ (1 + 3)). 
Compute of_N ((~ 1) + 3). 

Compute mask_ws. 

Compute mask_ws +ws mask_ws. 

Definition IV := 
  HexString.to_N("0x7380166f4914b2b9172442d7da8a0600a96f30bc163138aae38dee4db0fb0e4e").

Compute IV. 

(* 0 <= j <= 63*)
Definition T (j : nat) : N := 
  if Nat.leb j 15 then HexString.to_N "0x79cc4519"  else HexString.to_N "0x7a879d8a". 
Compute T 15. 
Compute T 16. 
(* 0 <= j <= 63, X Y Z are words*)
Definition FF (j : nat) (X : N)(Y : N)(Z : N) : N :=
  if Nat.leb j 15 then X $ Y $ Z else
  (X /\ Y) \/ (X /\ Z) \/ (Y /\ Z). 
Definition GG (j : nat) (X : N)(Y : N)(Z : N) : N :=
  if Nat.leb j 15 then X $ Y $ Z else
  (X /\ Y) \/ ((~ X) /\ Z). 

(*Example fact : forall X Z : N, (~ X /\ Z) = (~ X) /\ Z.  /\ (Y /\ Z). *)

Definition P0 (X : N) := X $ (X <<< 9) $ (X <<< 17).
Definition P1 (X : N) := X $ (X <<< 15) $ (X <<< 23).

Compute modulo 13 5. 
Compute Z.modulo (-13)%Z 5%Z. 

Compute log2 3. 
Compute size 31. 
Compute size 0. 
Compute to_N "0b11". 

Definition pad_k (l : N) :=
  Z.to_N (Z.modulo (Z.sub 447%Z (Z.of_N l)) 512). 

Compute pad_k 1.
Compute pad_k 512.
Compute pad_k 1024.

Compute iter 3 (fun (s : string) => append s "1"%string) "01"%string.  

Definition binaryStr (n : N) :=
  substring 2 (length (BinaryString.of_N n)) (BinaryString.of_N n). 

Definition prePad64(s : string) :=
  append (iter (64 - (N.of_nat (length s))) (fun s => append s "0"%string) ""%string) s. 

Compute binaryStr 3. 
Compute binaryStr 0. 
Compute binaryStr 24. 
Compute length (binaryStr 24). 
Compute prePad64 (binaryStr 24). 
Compute BinaryString.of_N 0. 

Definition Padding (m : string) (l : N) : string :=
  append ( iter (pad_k l) (fun (s : string) => append s "0"%string) (append m "1"%string)
  ) (prePad64 (binaryStr l)). 

Compute Padding "011000010110001001100011" 24. 

Compute shiftr 3 1.

Definition n_of_B (l : N) := div (l + (pad_k l) + 65) 512. 

Definition Block (i : nat)(m : string)(l : N) : N :=
  BinaryString.to_N ("0b" ++ (substring (i * 512) 512 (Padding m l))).

Compute Block 0 "011000010110001001100011" 24. 
Compute Block 1 "011000010110001001100011" 24. 
Compute Block 2 "011000010110001001100011" 24. 
Compute Block 0 "0" 1. 
Compute Block 0 "1" 1. 

Fixpoint W_slow (j : nat) (Bi : N) {struct j} : N :=
  match (j - 15)%nat with 
  (* j <= 15 *)
  | O => ((shiftr Bi ((N.of_nat (Nat.sub 15 j)) * word_size)) /\ mask_ws)
  | S j_16 (* j_16 = j - 16 *)=> 
     match j with
     | S (S (S j_3)) => 
         match j_3 with
         | S (S (S j_6)) =>
             match j_6 with
             | S (S (S j_9)) =>
               match j_9 with
               | S(S (S (S j_13))) => 
                  P1 ( (W_slow j_16 Bi) $ (W_slow j_9 Bi) $ (W_slow j_3 Bi) <<< 15)
                  $ (W_slow j_13 Bi) <<< 7 $ (W_slow j_6 Bi)
               | _ => 0 (* impossible *)
               end
             | _ => 0 (* impossible *)
             end
         | _ => 0 (* impossible *)
         end
     | _ => 0 (* impossible *)
     end
  end.

(* j <= 15 *)
Fixpoint W_list_init (j : nat)(Bi : N) : list N :=
  match j with
  | O => [(shiftr Bi (15 * word_size)) /\ mask_ws]
  | S j' => 
      ((shiftr Bi ((N.of_nat (Nat.sub 15 j)) * word_size)) /\ mask_ws)
      :: W_list_init j' Bi
  end. 

Definition W_list_aux (l' : list N) : list N :=
  (P1 ((List.nth 15 l' 0) $ (List.nth 8 l' 0) $ (List.nth 2 l' 0) <<< 15)
    $ (List.nth 12 l' 0) <<< 7 $ (List.nth 5 l' 0))
    :: l'. 

Fixpoint W_list (j : nat)(Bi : N) {struct j}: list N :=
  match (j - 15)%nat with
  | O => W_list_init j Bi (* j <= 15 *)
  | S j_16 => (* j_16 = j - 16 *)
      match j with
      | O => [] (* impossible *)
      | S j' => W_list_aux (W_list j' Bi)
      end
  end.

Definition W (j : nat)(Bi : N) :=
  List.nth 0 (W_list j Bi) 0. 

(*
Require Import FunInd.
Require Import Recdef.
Function W (j : N) (Bi : N) {measure j} : N :=
  if N.leb j 15 then ((shiftr Bi (15 - j) * word_size) /\ mask_ws) else
  P1 ( (W (j - 16) Bi) $ (W (j - 9) Bi) $ ((W (j - 3) Bi) <<< 15) $ ((W (j - 13) Bi) <<< 7) $ (W (j - 6) Bi) ).

Definition W (j : nat) (Bi : N)  : N :=
  (shiftr Bi (15 - (N.of_nat j)) * word_size) /\ mask_ws. 

Definition Wv_aux (v : penta) :=  P1 ( (1st v)$ (2nd v) $ ((3rd v) <<< 15) 
  $ ((4th v) <<< 7) $ (5th v).
(* Wv_j = ( W_(j), W_(j + 7), W_(j + 13), W_(j + 3), W_(j + 10) ) , j <= 51*)
Definition Wv (j : nat) (Bi : N) : N:= 
  match j with
  | 0 => ( (W 0 Bi), (W 7 Bi), (W 13 Bi), (W 3 Bi), (W 10 Bi) )
  | S j' =>
      *)

Definition Bitest := HexString.to_N "0x1111222233334444555566667777888899990000aaaabbbbccccddddeeeeffff1111222233334444555566667777888899990000aaaabbbbccccdd1deeeeffff". 
Compute HexString.of_N (W 0 Bitest).  
Compute HexString.of_N (W 1 Bitest).  
Compute HexString.of_N (W 15 Bitest).  
Compute HexString.of_N (W 14 Bitest).  

(* j <= 63 *)
Definition W' (j : nat) (Bi : N) :=
  (W j Bi) $ (W (j + 4) Bi). 

Compute shiftr 1 1. 
(* reg is 256 bit, i.e. 8 words. A is 1 word *)  
Definition Part_A (reg : N) : N := (shiftr reg (7 * word_size)) /\ mask_ws. 
Definition Part_B (reg : N) : N := (shiftr reg (6 * word_size)) /\ mask_ws. 
Definition Part_C (reg : N) : N := (shiftr reg (5 * word_size)) /\ mask_ws. 
Definition Part_D (reg : N) : N := (shiftr reg (4 * word_size)) /\ mask_ws. 
Definition Part_E (reg : N) : N := (shiftr reg (3 * word_size)) /\ mask_ws. 
Definition Part_F (reg : N) : N := (shiftr reg (2 * word_size)) /\ mask_ws. 
Definition Part_G (reg : N) : N := (shiftr reg (1 * word_size)) /\ mask_ws. 
Definition Part_H (reg : N) : N := reg /\ mask_ws. 

Definition SS1 (reg : N)(j : nat) : N :=
  ( ((Part_A reg) <<< 12) +ws (Part_E reg) +ws 
    ((T j) <<< (modulo (N.of_nat j) 32)) ) <<< 7.
(* mod 32 appears on the new version of SM3, which makes no
* difference in my implementation *)
Definition SS2 (reg : N) (j : nat) :=
  (SS1 reg j) $ ((Part_A reg) <<< 12). 
Definition TT1 (reg : N)(j : nat)(Bi : N) :=
  (FF j (Part_A reg) (Part_B reg) (Part_C reg)) +ws (Part_D reg) +ws (SS2 reg j) +ws (W' j Bi). 
Definition TT2 (reg : N)(j : nat)(Bi : N) :=
  (GG j (Part_E reg) (Part_F reg) (Part_G reg)) +ws (Part_H reg) +ws (SS1 reg j) +ws (W j Bi). 

Definition Reg_aux (reg : N)(j : nat)(Bi : N) :=
  (shiftl (TT1 reg j Bi) (7 * word_size)) \/
  (shiftl (Part_A reg) (6 * word_size)) \/
  (shiftl ((Part_B reg) <<< 9) (5 * word_size)) \/
  (shiftl (Part_C reg) (4 * word_size)) \/
  (shiftl (P0 (TT2 reg j Bi)) (3 * word_size)) \/
  (shiftl (Part_E reg) (2 * word_size)) \/
  (shiftl ((Part_F reg) <<< 19) (1 * word_size)) \/
  (Part_G reg). 


(* j in [0, 64] Vi is of 256 bit *)
Fixpoint Reg (j : nat) (Vi : N) (Bi : N) :=
  match j with
  | O => Vi
  | S j' =>
      Reg_aux (Reg j' Vi Bi) j' Bi
  end.

Definition CF (Vi : N) (Bi : N) :=
  (Reg 64 Vi Bi) $ Vi. 

Fixpoint V (i : nat)(m : string)(l : N) : N :=
  match i with
  | O => IV
  | S i' => CF (V i' m l) (Block i' m l)
  end.

Definition Hash (m : string) : N :=
  V (N.to_nat (n_of_B (N.of_nat (length m)))) m (N.of_nat (length m)). 

Definition hex2bin_with_prefix (m_hex : string) :=
  BinaryString.of_N (HexString.to_N ("0x" ++ m_hex)). 

Definition remove_prefix (s : string) (pre_len : nat) : string :=
  substring pre_len (length s) s.  

Definition pre_pad_0 (s : string)(mod_size : N) : string :=
  Z.iter (Z.modulo (Z.opp (Z.of_nat (length s))) (Z.of_N mod_size)) (append "0") s. 

Definition hex2bin (m_hex : string) :=
  remove_prefix (hex2bin_with_prefix m_hex) 2. 

Definition bin2hex (m_bin : string) :=
  remove_prefix (HexString.of_N (BinaryString.to_N ("0b" ++ m_bin))) 2. 

Definition Hash_hex (m_hex : string) :=
  Hash (pre_pad_0 (hex2bin m_hex) 4).  

Definition exp_m := "616263".  
Definition exp_padded := bin2hex (Padding (hex2bin exp_m) (6 * 4)). 
Compute exp_padded. 

Definition B0 := (Block 0 (hex2bin exp_m) (6 * 4)).

Compute HexString.of_N B0. 
Compute HexString.of_N (W 67 B0).  (* Correct. *)
Compute HexString.of_N (W 0  B0).  (* Correct. *)
Compute HexString.of_N (W 15  B0).  (* Correct. *)
Compute HexString.of_N (W 14  B0).  (* Correct. *)
Compute HexString.of_N (W' 63 B0). (* Correct. *) 
Compute HexString.of_N (W' 1 B0). (* Correct. *) 
Compute hex2bin exp_m. 
Compute n_of_B 24.
Compute HexString.of_N (V 1 "011000010110001001100011" 24). 

Compute HexString.of_N IV. 
Compute HexString.of_N (Reg 0 IV B0). 
Compute HexString.of_N (Reg 1 IV B0). (*Correct*)
Compute HexString.of_N (Reg 64 IV B0). (*Correct*)
Compute HexString.of_N ((Reg 64 IV B0) $ IV). (*Correct*)

(* "0x66c7f0f462eeedd9d1f2d46bdc10e4e24167c4875cf2f7a2297da02b8f4ba8e0" *)
Compute HexString.of_N (Hash "011000010110001001100011"). (* Correct *) 
Compute HexString.of_N (Hash_hex exp_m). (* Correct *) 

Definition exp_m2 := "61626364616263646162636461626364616263646162636461626364616263646162636461626364616263646162636461626364616263646162636461626364".
(*debe9ff9 2275b8a1 38604889 c18e5a4d 6fdb70e5 387e5765 293dcba3 9c0c5732*)
Compute HexString.of_N (Hash_hex exp_m2). (* Correct *) 
