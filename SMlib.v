Require Export Coq.PArith.BinPosDef. 
Require Export Coq.Strings.BinaryString. 
Require Export Coq.Strings.HexString. 
Require Export Ascii String. 
Require Export Coq.Strings.Ascii. 
Require Export Coq.Strings.String. 
Require Export Tables. 
Require Export NArith.
Require Export CCompLib.Integers.

Export N. 
Definition word_size := 32%N. 
Definition half_word_size := 16%N. 
Definition modulus := shiftl 1 word_size.
Definition half_modulus := shiftl 1 half_word_size.  
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
  shiftr_cyc n (word_size - t). 

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

Definition quad2N (q : @quadruple N) : N :=
  (shiftl (q1st q) (word_size * 3)) + 
  (shiftl (q2nd q) (word_size * 2)) + 
  (shiftl (q3rd q) (word_size * 1)) + 
  (q4th q). 

Definition N2quad (x : N) : quadruple := 
  ((mask_14 x), (mask_24 x), (mask_34 x), (mask_44 x)). 

Definition quadN2quadX (q : quadruple) : quadruple :=
  (of_N (q1st q), of_N (q2nd q), of_N (q3rd q), of_N (q4th q)). 

Definition pentad {X : Type} : Type := X * X * X * X * X. 
Definition p1st {X : Type} (v : pentad) : X :=
  match v with
  | (x, _, _, _, _) => x
  end.
Definition p2nd {X : Type} (v : pentad) : X :=
  match v with
  | (_, x, _, _, _) => x
  end.
Definition p3rd {X : Type} (v : pentad) : X :=
  match v with
  | (_, _, x, _, _) => x
  end.

Definition p4th {X : Type} (v : pentad) : X :=
  match v with
  | (_, _, _, x, _) => x
  end.

Definition p5th {X : Type} (v : pentad) : X :=
  match v with
  | (_, _, _, _, x) => x
  end.

