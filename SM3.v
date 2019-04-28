Require Import SMlib.
Require Import Coq.ZArith.BinIntDef.  
Require Import Coq.Strings.BinaryString. 

Locate "~". 
Locate "+".

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
  m + n /\ mask_ws.  

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
  if leb j 15 then to_N "0x79cc4519"  else to_N "0x7a879d8a". 
(* 0 <= j <= 63, X Y Z are words*)
Definition FF (j : N) (X : N)(Y : N)(Z : N) : N :=
  if leb j 15 then X $ Y $ Z else
  (X /\ Y) \/ (X /\ Z) \/ (Y /\ Z). 
Definition GG (j : N) (X : N)(Y : N)(Z : N) : N :=
  if leb j 15 then X $ Y $ Z else
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


