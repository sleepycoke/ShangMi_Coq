Require Import SMlib.
Require Import Coq.ZArith.BinIntDef.  
Require Import Coq.Strings.BinaryString. 
Require Import Program Arith.

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

Compute mask_ws +ws 1. 

Definition IV := 
  to_N("0x7380166f4914b2b9172442d7da8a0600a96f30bc163138aae38dee4db0fb0e4e").

Compute IV. 

(* 0 <= j <= 63*)
Definition T (j : N) : N := 
  if N.leb j 15 then to_N "0x79cc4519"  else to_N "0x7a879d8a". 
(* 0 <= j <= 63, X Y Z are words*)
Definition FF (j : N) (X : N)(Y : N)(Z : N) : N :=
  if N.leb j 15 then X $ Y $ Z else
  (X /\ Y) \/ (X /\ Z) \/ (Y /\ Z). 
Definition GG (j : N) (X : N)(Y : N)(Z : N) : N :=
  if N.leb j 15 then X $ Y $ Z else
  (X /\ Y) \/ (~ X /\ Z). 

(*Example fact : forall X Z : N, (~ X /\ Z) = (~ X) /\ Z.  /\ (Y /\ Z). *)

Definition P0 (X : N) := X $ X <<< 9 $ X <<< 17.
Definition P1 (X : N) := X $ X <<< 15 $ X <<< 23.

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

(*B is 512 bit, W j is 16 bit, j <= 67*)
(* ill-formed *)
(*
Fixpoint W (j : N) (Bi : N) {struct j} : N :=
  if leb j 15 then ((shiftr Bi (15 - j) * word_size) /\ mask_ws) else
  P1 ( (W (j - 16) Bi) $ (W (j - 9) Bi) $ ((W (j - 3) Bi) <<< 15) $ ((W (j - 13) Bi) <<< 7) $ (W (j - 6) Bi) ).
*)
(* j <= 15 *)
Fixpoint W (j : nat) (Bi : N) {struct j} : N :=
  match j with
  | S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S j_16))))))))))))))) (* j_16 = j - 16 *)=> 
     match j with
     | S (S (S j_3)) => 
         match j_3 with
         | S (S (S j_6)) =>
             match j_6 with
             | S (S (S j_9)) =>
               match j_9 with
               | S(S (S (S j_13))) => 
                  P1 ( (W j_16 Bi) $ (W j_9 Bi) $ (W j_3 Bi) <<< 15)
                  $ (W j_13 Bi) <<< 7 $ (W j_6 Bi)
               | _ => 0 (* impossible *)
               end
             | _ => 0 (* impossible *)
             end
         | _ => 0 (* impossible *)
         end
     | _ => 0 (* impossible *)
     end
  | _ => ((shiftr Bi ((N.of_nat (Nat.sub 15 j)) * word_size)) /\ mask_ws) (* j <= 15 *)
  end.
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

(* Vi is 256 bit, i.e. 8 words. a is 1 word *)  
Definition A' (Vi : N) : N := (Vi >>> 7) /\ mask_ws. 
Definition B' (Vi : N) : N := (Vi >>> 6) /\ mask_ws. 
Definition C' (Vi : N) : N := (Vi >>> 5) /\ mask_ws. 
Definition D' (Vi : N) : N := (Vi >>> 4) /\ mask_ws. 
Definition E' (Vi : N) : N := (Vi >>> 3) /\ mask_ws. 
Definition F' (Vi : N) : N := (Vi >>> 2) /\ mask_ws. 
Definition G' (Vi : N) : N := (Vi >>> 1) /\ mask_ws. 
Definition H' (Vi : N) : N := Vi /\ mask_ws. 

Definition SS1 (Vi : N)(j : N) : N :=
  (( (A' Vi) <<< 12 ) +ws (E' Vi) +ws ((T j) <<< j)) <<< 7.
Definition SS2 (Vi : N) (j : N) :=
  (SS1 Vi j) $ (A' Vi) <<< 12. 
Definition TT1 (Vi : N)(j : N)(Bi : N) :=
  (FF j (A' Vi) (B' Vi) (C' Vi)) +ws (D' Vi) +ws (SS2 Vi j) +ws (W' (N.to_nat j) Bi). 
Definition TT2 (Vi : N)(j : N)(Bi : N) :=
  (GG j (E' Vi) (F' Vi) (G' Vi)) +ws (H' Vi) +ws (SS1 Vi j) +ws (W (N.to_nat j) Bi ). 

Definition A := TT1.
Definition B := A'. 
Definition C (Vi : N) := (B' Vi) <<< 9.
Definition D := C'. 
Definition E (Vi : N)(j : N)(Bi : N)  := P0 (TT2 Vi j Bi).
Definition F := E'. 
Definition G (Vi : N) := (F' Vi) <<< 19. 
Definition H := G'. 

Definition CF (Vi : N) (Bi : N) :=
  A (

Fixpoint V (i : nat) : N :=
  match i with
  | O => IV. 
  | 

