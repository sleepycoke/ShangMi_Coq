Require Export Coq.PArith.BinPosDef. 
Require Export Coq.ZArith.BinIntDef.  
Require Export Coq.Strings.BinaryString. 
Require Export Coq.Strings.HexString. 
Require Export Ascii String. 
Require Export Coq.Strings.Ascii. 
Require Export Coq.Strings.String. 
Require Export Coq.Lists.List.
Require Export NArith.

Require Export Constants. 
Require Export Byte. 

Export ListNotations. 

Export N. 
Definition word_size := 32%N. 
Definition half_word_size := 16%N. 
Definition modulus_ws := shiftl 1 word_size.
Definition half_modulus_ws := div2 modulus_ws.  
Definition hfws_modulus := shiftl 1 half_word_size.  
Definition mask_ws := sub modulus_ws 1. 
Definition mask_hfws := sub half_modulus_ws 1. 


Definition shiftr1_cyc (len : N)(n : N) : N := 
  let half_modulus := shiftl 1 (len - 1) in
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
Definition shiftr_cyc (len : N)(n : N) (t : N) : N :=
  N.iter t (shiftr1_cyc len) n. 
 
Definition shiftr_cyc_ws := shiftr_cyc word_size. 

Infix ">>>" := shiftr_cyc_ws (at level 35). 

Definition shiftl_cyc (len : N)(n: N) (t : N) : N :=
  shiftr_cyc len n (len - (t mod len)). 

Definition shiftl_cyc_ws := shiftl_cyc word_size. 

Infix "<<<" := shiftl_cyc_ws (at level 35). 
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

(* Replace old with acc within s *)
Fixpoint RepChar_tail (s : string)(old : ascii)(new acc : string) : string :=
  match s with
  | "" => acc
  | String h t => 
      RepChar_tail t old new (acc ++
        if Ascii.eqb h old then new else (String h "")
      )
  end. 

Definition RepChar (s : string)(old : ascii)(new : string) : string :=
  RepChar_tail s old new "". 


(* returns the prefix of length k * the rest *)
Fixpoint partList_tail (A : Type)(l : list A)(len : nat)(acc : list A * list A) : list A * list A :=
  match len with
  | O => acc
  | S len' =>
      match l with
      | [] => acc
      | h :: tl =>
          partList_tail A tl len' ((List.app (fst acc) [h]), List.tl (snd acc))
      end
  end.

Definition partList {A} (l : list A)(len : nat) :=
  partList_tail A l len ([], l). 

Definition partListBack {A} (l : list A)(backLen : nat) :=
  partList l ((List.length l) - backLen).

Fixpoint subList_tail {A} (start : nat)(length : nat)(l : list A)(acc : list A) :=
  match l with
  | [] => acc
  | h :: tl =>
    match start with
    | S start' => subList_tail start' length tl acc
    | O =>
       match length with
       | O => acc
       | S length' =>
          subList_tail start length' tl (acc ++ [h])
       end
    end
  end.  

Definition subList {A} (start : nat)(length : nat)(l : list A) :=
  subList_tail start length l [].


(* ceil(x/y) *)
Definition div_ceil_nat (x : nat)(y : nat) : nat :=
  Nat.div (x + y - 1%nat) y. 
Definition div_ceil_N (x : N)(y : N) : N :=
  N.div (x + y - 1%N) y. 


Inductive optErr (A : Type) : Type :=
| Normal : A -> optErr A
| Error : string -> optErr A. 

Arguments Normal {A} _.
Arguments Error {A}.

Fixpoint Nlist_tail (k : nat)(acc : list N) : list N :=
  match k with
  | O => acc
  | S k' =>
      Nlist_tail k' ((N.of_nat k') :: acc)
  end.

(*Generates [0; 1; 2; ... ; len - 1]*)
Definition Nlist (len : N) : list N :=
  Nlist_tail (N.to_nat len) [].

(* Try each element x in l with func : option N. 
* If func x is not None then return its value otherwise keep trying. 
* If all None then return None. *)
Fixpoint TryFunWithList (func : N -> option N)(l : list N) : option N :=
  match l with
  | [] => None
  | x :: tl =>
      match func x with
      | Some y => Some y
      | None => TryFunWithList func tl 
      end
  end. 



(*funcs upon prefix..XXXX, where XXXX is of length len *) 
Fixpoint BinaryMapLen_fix (func : N -> N)(len : nat)(prefix : N) : list N :=
  match len with
  | O => [func prefix] (* only one number *)
  | S len' => 
      (BinaryMapLen_fix func len' (double prefix)) ++ (* appending a 0 to prefix, len-- *)
      (BinaryMapLen_fix func len' (succ_double prefix)) (* appending a 1 to prefix, len-- *)
  end. 

(*maps func on all Ns within length len*)
Definition BinaryMapLen (func : N -> N)(len : nat) : list N :=
  BinaryMapLen_fix func len 0. 

(*
Compute BinaryMapLen N.square 4. (*Correct*)
*)


Open Scope list_scope. 
(* This approach does work. But accumulated modifying func could be too complicated *)
(*
Fixpoint BinaryMap_pos (func : positive -> N)(p : positive) : list N :=
  let sub := fun x => (BinaryMap_pos func x) ++ (* maps [1,  x] *)
      (BinaryMap_pos (fun y => func (Pos.add y x)) x) in (* maps [x + 1, 2x] *)
  match p with
  | xH => [func p]
  | xO p' => sub p'
  | xI p' => sub p' ++ [func p]
  end. 

Definition BinaryMap (func : N -> N)(n : N) : list N :=
  match n with
  | N0 => [func N0]
  | Npos p => [func N0] ++ (BinaryMap_pos (fun x => func (Npos x)) p)
  end. 

Compute BinaryMap N.square 20. (* Correct *) 
*)

Fixpoint BinaryMap_pos (func : positive -> N)(p : positive)(base : N) : list N :=
  let current := match base with
  | N0 => [func p]
  | Npos q => [func (Pos.add p q)]
  end in
  let sub := fun x => (BinaryMap_pos func x base) ++ (* maps [1,  x] *)
      (BinaryMap_pos func x (base + (Npos x))) in (* maps [x + 1, 2x] *)
  match p with
  | xH => current
  | xO p' => sub p'
  | xI p' => sub p' ++ current
  end. 

Definition BinaryMap (func : N -> N)(n : N) : list N :=
  match n with
  | N0 => [func N0]
  | Npos p => [func N0] ++ (BinaryMap_pos (fun x => func (Npos x)) p 0)
  end. 

(*
Compute BinaryMap N.square 10. (* Correct *) 
*)
(*
Time Compute BinaryMap N.square 10000. (* Correct *) 
Finished transaction in 1.209 secs 
Both approach cost nearly the same time. 
*)

(* TODO Consider utilizing TryBinary_Len for each 1 from left to right after NtobL *)
(* Finds the first positive in [1, p] that trusifies func. *)
Fixpoint TryBinary_fix (func : positive -> bool)(p : positive)(base : N) : option positive :=
  let shifted := match base with
  | N0 => p
  | Npos q => Pos.add p q
  end in
  let sub := 
    fun x => 
      match TryBinary_fix func x base with
      | Some r => Some r
      | None => TryBinary_fix func x (base + (Npos x))
      end in
  match p with
  | xH => if func shifted then Some shifted else None
  | xO p' => sub p'
  | xI p' => 
      match sub p' with
      | Some r => Some r
      | None => if func shifted then Some shifted else None
      end
  end.


Definition TryBinary_pos (func : positive -> bool)(p : positive) : option positive :=
  TryBinary_fix func p 0. 

(*
Compute TryBinary_pos (Pos.leb 5) 4. 
Compute TryBinary_pos (Pos.leb 5) 40. 
*)

Definition TryBinary (func : N -> bool)(n : N) : option N :=
  match n with 
  | N0 => if func N0 then Some N0 else None
  | Npos p => 
      match TryBinary_pos (fun x => func (Npos x)) p with
      | Some r => Some (Npos r)
      | None => None
      end
  end. 

(*
Compute TryBinary (N.leb 5) 40. 
Compute TryBinary (N.leb 5) 0. 
*)

Definition TryBinarySampler (func : N -> bool)(smpl : N -> N)(n : N) :=
	TryBinary (fun x => func(smpl x)) n. 

Fixpoint TryBinaryLen_fix (func : N -> bool)(len : nat)(prefix : N) : option N :=
  match len with
  | O => if func prefix then Some prefix else None
  | S len' =>
      match TryBinaryLen_fix func len' (double prefix) with
      | Some n => Some n
      | None => TryBinaryLen_fix func len' (succ_double prefix)
      end
  end.

(*Find the smallest N within length len that satisfies func *)
Definition TryBinaryLen (func : N -> bool)(len : nat) : option N :=
  TryBinaryLen_fix func len 0. 

(*
Compute (fix func (x : nat) : nat := 
  match x with
  | O => 1%nat
  | S x' => Nat.mul x (func x') 
  end)
  5%nat. 
  *)

(*
Compute TryBinaryLen (fun x => leb 20 x) 4. 
Compute TryBinaryLen (fun x => leb 20 x) 5. 
Compute TryBinaryLen (fun x => leb 20 x) 6. 
Compute TryBinaryLen (fun x => leb 20000000 x) 2000. 
Correct *)

Inductive timed (A : Type)(B : Type) : Type :=
(* the process returns A within the time limit *)
| Cvg : A -> timed A B 
(* the process did not halt in time, not sure would ever halt *)
(* Returns B for continued process *)
| Tmo : B -> timed A B 
(* the process would never halt *)
| Dvg : timed A B 
.

Arguments Cvg {A} {B} _.
Arguments Dvg {A} {B}.
Arguments Tmo {A} {B} _.

Fixpoint TryTrans_fix (A : Type)(func : N -> option A)(trans : N -> N)(initial : N)(last : N)
  (loop_count : positive) : timed A N :=
  let check_dvg := 
      fun x : N =>
        (let next := trans x in
          if next =? initial then Dvg else Tmo next) in
  match loop_count with
  | xH =>
    match func last with
    | Some r => Cvg r
    | None => check_dvg last
    end
  | xO lc' | xI lc' =>
    (*if andb (negb first_pass) (last =? initial) then Dvg else (* finished a period *)*)
    match TryTrans_fix A func trans initial last lc' with
    | Cvg r => Cvg r
    | Dvg => Dvg
    | Tmo trans_r => 
        match TryTrans_fix A func trans initial trans_r lc' with
        | Cvg r => Cvg r
        | Dvg => Dvg
        | Tmo trans_r' => 
            match loop_count with
            | xO lc' => Tmo trans_r' 
            | _ => 
                match func trans_r' with
                | Some r => Cvg r
                | None => check_dvg trans_r'
                end
            end
        end
    end
  end.

(* If func returns Some A within loop_limit tests, then return Cvg *)
(* If a period has been traversed, then return Dvg *)
(* O.W. returns Imo next_input *)
Definition TryTrans (A : Type)(func : N -> option A)(trans : N -> N)(initial : N)
  (loop_limit : N) : timed A N :=
  match loop_limit with
  | N0 => Tmo initial
  | Npos lp =>
      TryTrans_fix A func trans initial initial lp 
      (*
      match TryTrans_fix A func trans initial initial lp true with
      | Dvg => Dvg
      | Cvg r => Cvg r
      | Tmo last =>
          if last =? initial then Dvg else Tmo last
      end
      *)
  end. 
 
 (*
(* 3 -> 3 *)
Compute TryTrans N (fun x => if (N.eqb 5 x) then Some x else None) (fun x => x mod 7) 3 2. 
Compute TryTrans N (fun x => if (N.eqb 5 x) then Some x else None) (fun x => x mod 7) 3 1. 
Compute TryTrans N (fun x => if (N.eqb 5 x) then Some x else None) (fun x => x mod 7) 3 0. 
            
(* 1 -> 2 -> 4 -> 1 *)
Compute TryTrans N (fun x => if (N.eqb 5 x) then Some x else None) (fun x => (N.double x) mod 7) 1 2 . 
Compute TryTrans N (fun x => if (N.eqb 5 x) then Some x else None) (fun x => (N.double x) mod 7) 1 3 . 
Compute TryTrans N (fun x => if (N.eqb 5 x) then Some x else None) (fun x => (N.double x) mod 7) 1 4 . 

(* 3 -> 6 -> 5 *)
Compute TryTrans N (fun x => if (N.eqb 5 x) then Some x else None) (fun x => (N.double x) mod 7) 3 0. 
Compute TryTrans N (fun x => if (N.eqb 5 x) then Some x else None) (fun x => (N.double x) mod 7) 3 1. 
Compute TryTrans N (fun x => if (N.eqb 5 x) then Some x else None) (fun x => (N.double x) mod 7) 3 2. 
Compute TryTrans N (fun x => if (N.eqb 5 x) then Some x else None) (fun x => (N.double x) mod 7) 3 7. 
*)
