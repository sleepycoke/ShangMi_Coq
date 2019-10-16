Require Export SMlib.
Require Export Coq.Strings.Ascii.

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

Fixpoint N2BL_tail (k : nat)(x : N)(acc : BL) : BL :=
  match k with
  | O => acc
  | S k' => 
      N2BL_tail k' (N.div x 256) (N2Byte (N.modulo x 256) :: acc)
  end.

(*4.2.1 trunk from right*)
Definition N2BL_len (k : nat)(x : N) : BL :=
  N2BL_tail k x [].

Compute N2BL_len 4 1025.

Definition N2BL (x : N) : BL :=
  N2BL_len (N.to_nat (N.div (N.add (N.size x) 7) 8)) x. 

Compute N2BL 1025 .
Compute N2BL 256 .
Compute N2BL 255 .

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

Compute partList [1;2;3] 0. 
Compute partList [1;2;3] 3. 
Compute partList [1;2;3] 4. 

Definition partListBack {A} (l : list A)(backLen : nat) :=
  partList l ((List.length l) - backLen).

Compute partListBack [1;2;3] 4. 
Compute partListBack [1;2;3] 2. 

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

Compute subList 1 2 [1;2;3]. 
Compute subList 0 2 [1;2;3]. 

(*4.2.3*)
Fixpoint bL2BL_tail (s : bL)(k : nat)(acc : BL) : BL :=
  match k with
  | O => acc 
  | S k' =>
      (fun sl => bL2BL_tail (fst sl) k' 
      (List.app [bL2Byte (snd sl) 8] acc)) (partListBack s 8)
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

(* [] for 0, trunk from right. *)
Definition N2bL_len (len : nat)(n : N) : bL :=
  N2bL_tail n len []. 

Definition N2bL (n : N) : bL :=
  N2bL_len (N.to_nat (N.size n)) n.

Compute N2bL 127. 
Compute N2bL 3. 
Compute N2bL 4. 
Compute N2bL 0. 


(*4.2.4*)
(*2019-10-09, realized that I need to keep preceding 0s 
* And it is only used in KeyEx.v yet. *)
Fixpoint BL2bL_tail (M : BL)(k : nat)(acc : bL) : bL :=
  match k with
  | O => acc
  | S k'=> 
      match M with
      | [] => acc
      | h :: tl =>
          BL2bL_tail tl k' (List.app acc (N2bL_len 8 (Byte.to_N h)))
      end
  end.

Definition BL2bL (M : BL) : bL :=
  BL2bL_tail M (List.length M) [].

Compute BL2bL [].
Compute BL2bL [xff].

Definition N2bS (n : N) : string :=
  bL2bS (N2bL n).

Definition N2bS_len (n : N)(len : nat) : string :=
  bL2bS (N2bL_len len n).

Compute N2bS 6. 
Definition rmsp (s : string) := (RepChar s " "%char ""%string). 
Fixpoint hS2bS_tail (m_hex : string)(acc : string) : string :=
  match m_hex with
  | "" => acc
  | String h tl =>
      match HexString.ascii_to_digit h with
      | None => ""
      | Some v => hS2bS_tail tl (acc ++ N2bS_len v 4)
      end
  end. 

Definition hS2bS (m_hex : string) : string :=
  hS2bS_tail (rmsp m_hex) "".

Print HexString.Raw.to_N. 
Definition hS2N (m_hex : string) : N :=
  HexString.Raw.to_N (rmsp m_hex) 0. 

(*
Definition hChar2bL (m_hex : string) : bL :=
  let rawbl := N2bL (hS2N m_hex) in
    List.app
    match (Nat.modulo (List.length rawbl) 4) with
    | 1%nat => [false; false; false] 
    | 2%nat => [false; false] 
    | 3%nat => [false]
    | _ => [false; false; false; false]
    end
    rawbl. 
    *)
Definition hS2bL (hs : string) :=
  bS2bL (hS2bS hs). 

Compute hS2bL "04F". 

Definition N2hS (n : N) : string :=
  match n with
  | Npos p => HexString.Raw.of_pos p ""
  | N0 => ""
  end.  

Definition N2hChar (n : N) : string :=
  match n with
  | Npos p => HexString.Raw.of_pos p ""
  | N0 => "0"
  end. 

Fixpoint bL2hS_tail (bl : bL)(hSLen : nat)(acc : string) : string :=
  match hSLen with
  | O => acc
  | S len' =>
  let (pre, suf) := partListBack bl 4 in
    match suf with
    | [] => acc
    | _ => bL2hS_tail pre len' ((N2hChar (bL2N suf)) ++ acc)
    end
  end.

Definition bL2hS (bl : bL) : string :=
  bL2hS_tail bl (Nat.div (Nat.add (length bl) 3%nat) 4%nat) "".

Compute bL2hS [true; false]. 
Compute bL2hS [false; false; false; false; false; false; true; false]. 

Compute bL2hS (BL2bL [x01; xff]).
Definition bS2hS (m_bin : string) : string :=
  bL2hS (bS2bL m_bin). 

Fixpoint str2bL_tail (s : string)(acc : bL) :=
  match s with
  | "" => acc
  | String c tl =>
      str2bL_tail tl (List.app acc (N2bL_len 8 (N_of_ascii c)))
  end. 

Definition str2bL (s : string) :=
  str2bL_tail s [].

Compute str2bL "". 
Compute bL2hS (str2bL "ALICE"). 
(*4.2.5*)

Inductive field_type : Set :=
  pri : field_type | ext : field_type .
Definition Field2BL_p (alpha : N) : BL :=
  N2BL_len (N.to_nat (N.div ((N.size alpha) + 7) 8)) alpha. 

Definition Field2BL_m (alpha : bL) :=
  bL2BL alpha. 

(*4.2.6*)
Definition BL2Field_p (Bl : BL)(q : N) : option N :=
  (fun (alpha : N)  => if leb q alpha then None else Some alpha) (BL2N Bl).  

Definition BL2Field_m (Bl : BL) : bL :=
  BL2bL Bl. 

Compute BL2Field_p [x07] 7. 
Compute BL2Field_p [x06] 7. 

(*4.2.7*)
Definition Field2N_m (alpha : bL) : N :=
  bL2N alpha. 

