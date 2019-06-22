Require Export Coq.PArith.BinPosDef. 
Require Export Coq.ZArith.BinIntDef.  
Require Export Coq.Strings.BinaryString. 
Require Export Coq.Strings.HexString. 
Require Export Ascii String. 
Require Export Coq.Strings.Ascii. 
Require Export Coq.Strings.String. 
Require Export Coq.Lists.List.
Export ListNotations.
Require Export NArith.

Require Export Tables. 
Require Export Byte. 


Export N. 
Definition word_size := 32%N. 
Definition half_word_size := 16%N. 
Definition modulus := shiftl 1 word_size.
Definition half_modulus := div2 modulus.  
Definition hfws_modulus := shiftl 1 half_word_size.  
Definition mask_ws := sub modulus 1. 
Definition mask_hfws := sub half_modulus 1. 


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

(* n >>> t*)
Definition shiftr_cyc (n : N) (t : N) : N :=
  N.iter t shiftr1_cyc n . 

Infix ">>>" := shiftr_cyc (at level 35). 

Definition shiftl_cyc (n: N) (t : N) : N :=
  shiftr_cyc n (word_size - (t mod word_size)). 

Infix "<<<" := shiftl_cyc (at level 35). 
Infix "$" := lxor (at level 50). 

Definition mask_14 (A : N) : N := 
  shiftr (land A (shiftl mask_ws (word_size * 3))) (word_size * 3). 
Definition mask_24 (A : N) : N := 
  shiftr (land A (shiftl mask_ws (word_size * 2))) (word_size * 2). 
Definition mask_34 (A : N) : N := 
  shiftr (land A (shiftl mask_ws (word_size * 1))) (word_size * 1). 
Definition mask_44 (A : N) : N := 
  land A mask_ws. 

(* https://en.cppreference.com/w/c/language/operator_precedence *)
(* Bit-wise operation are below + -*)
Infix "/\" := N.land : N_scope.
Infix "\/" := N.lor : N_scope.
(* ~ n with respect to word_size *)
Definition neg_ws (n : N) : N := 
  n $ mask_ws. 
Notation "~ n" := (neg_ws n) (at level 75, right associativity) : N_scope. 

Definition add_ws (m : N)(n : N) : N := 
  (m + n) /\ mask_ws.  

Infix "+ws" := add_ws (at level 50): N_scope. 
