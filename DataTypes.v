Require Export SMlib.
Require Export Coq.Strings.Ascii.

(* ByteList is indeed a list of bytes*)
Definition BL := list byte. 
(* BitList is indeed a list of bool*)
Definition bL := list bool. 
Fixpoint bStobL_tail (bs : string)(acc : bL) : bL :=
  match bs with
  | EmptyString => acc 
  | String head tl =>
      match ascii_to_digit head with
      | Some 1 => bStobL_tail tl (List.app acc [true])
      | _ => bStobL_tail tl (List.app acc [false])
      end
  end.

Open Scope list_scope. 

Definition bStobL (bs : string) : bL :=
  bStobL_tail bs []. 

Fixpoint bLtobS_tail (bl : bL)(acc : string) : string :=
  match bl with
  | [] => acc
  | head :: tl =>
      match head with
      | true => bLtobS_tail tl (acc ++ "1")
      | false => bLtobS_tail tl (acc ++ "0")
      end
  end.

Definition bLtobS (bl : bL) : string :=
  bLtobS_tail bl "". 

Fixpoint BLtoN_tail (Bl : BL)(acc : N) : N :=
  match Bl with
  | [] => acc
  | h :: tl =>
      BLtoN_tail tl (acc * 256 + (Byte.to_N h)) 
  end.

(*4.2.2*)
Fixpoint BLtoN (Bl : BL) : N :=
  BLtoN_tail Bl 0.

Definition NtoByte (n : N) : byte :=
  match Byte.of_N n with
  | None => x00
  | Some b => b
  end.

Fixpoint NtoBL_tail (k : nat)(x : N)(acc : BL) : BL :=
  match k with
  | O => acc
  | S k' => 
      NtoBL_tail k' (N.div x 256) (NtoByte (N.modulo x 256) :: acc)
  end.

(*4.2.1 trunk from right*)
Definition NtoBL_len (k : nat)(x : N) : BL :=
  NtoBL_tail k x [].

Definition NtoBL (x : N) : BL :=
  NtoBL_len (N.to_nat (N.div (N.add (N.size x) 7) 8)) x. 

(* Transform the first k(<= 8) bits into an N *)  
Fixpoint bLtoN_tail (bl : bL)(k : nat)(acc : N) : N :=
  match k with
  | O => acc
  | S k' => 
      match bl with
      | [] => acc
      | h :: tl => 
          match h with
          | false => bLtoN_tail tl k' (N.double acc)
          | true => bLtoN_tail tl k' (N.add 1 (N.double acc))
          end
      end
  end.

(*4.2.2*)
Definition bLtoN (bl : bL) :=
  bLtoN_tail bl (List.length bl) 0.

Definition bLtoN_prefix (bl :bL)(k : nat) : N :=
  bLtoN_tail bl k 0.

(* tranfrom the first k bits into a byte *)
Definition bLtoByte (bl : bL)(k : nat) :=
  NtoByte (bLtoN_prefix bl k). 



(*4.2.3*)
Fixpoint bLtoBL_tail (s : bL)(k : nat)(acc : BL) : BL :=
  match k with
  | O => acc 
  | S k' =>
      (fun sl => bLtoBL_tail (fst sl) k' 
      (List.app [bLtoByte (snd sl) 8] acc)) (partListBack s 8)
  end.


Definition bLtoBL (s : bL) : BL :=
  bLtoBL_tail s (Nat.div (Nat.add(List.length s) 7%nat) 8%nat) []. 

Fixpoint NtobL_tail (n : N)(k : nat)(acc : bL) : bL :=
  match k with
  | O => acc
  | S k' => 
      NtobL_tail (N.div n 2) k' (N.odd n :: acc)
  end.

(* [] for 0, trunk from right. *)
Definition NtobL_len (len : nat)(n : N) : bL :=
  NtobL_tail n len []. 

Definition NtobL (n : N) : bL :=
  NtobL_len (N.to_nat (N.size n)) n.

Definition bStoN (bs : string) : N :=
  bLtoN (bStobL bs). 


(*4.2.4*)
(*2019-10-09, realized that I need to keep preceding 0s 
* And it is only used in KeyEx.v yet. *)
Fixpoint BLtobL_tail (M : BL)(k : nat)(acc : bL) : bL :=
  match k with
  | O => acc
  | S k'=> 
      match M with
      | [] => acc
      | h :: tl =>
          BLtobL_tail tl k' (List.app acc (NtobL_len 8 (Byte.to_N h)))
      end
  end.

Definition BLtobL (M : BL) : bL :=
  BLtobL_tail M (List.length M) [].

Definition NtoBbL (n : N) : bL := BLtobL (NtoBL n). 

(*Padding len to a multiplier of 8*)
(*Croping from the rightside *)
Definition NtoBbL_len (len : nat)(n : N) : bL := 
  BLtobL (NtoBL_len (div_ceil_nat len 8%nat) n). 

Definition NtobS (n : N) : string :=
  bLtobS (NtobL n).

Definition NtobS_len (n : N)(len : nat) : string :=
  bLtobS (NtobL_len len n).

Definition rmsp (s : string) := (RepChar s " "%char ""%string). 
Fixpoint hStobS_tail (m_hex : string)(acc : string) : string :=
  match m_hex with
  | "" => acc
  | String h tl =>
      match HexString.ascii_to_digit h with
      | None => ""
      | Some v => hStobS_tail tl (acc ++ NtobS_len v 4)
      end
  end. 

Definition hStobS (m_hex : string) : string :=
  hStobS_tail (rmsp m_hex) "".

Definition hStoN (m_hex : string) : N :=
  HexString.Raw.to_N (rmsp m_hex) 0. 

(*
Definition hChartobL (m_hex : string) : bL :=
  let rawbl := NtobL (hStoN m_hex) in
    List.app
    match (Nat.modulo (List.length rawbl) 4) with
    | 1%nat => [false; false; false] 
    | 2%nat => [false; false] 
    | 3%nat => [false]
    | _ => [false; false; false; false]
    end
    rawbl. 
    *)
Definition hStobL (hs : string) :=
  bStobL (hStobS hs). 

Definition NtohS (n : N) : string :=
  match n with
  | Npos p => HexString.Raw.of_pos p ""
  | N0 => ""
  end.  

Definition NtohChar (n : N) : string :=
  match n with
  | Npos p => HexString.Raw.of_pos p ""
  | N0 => "0"
  end. 

Fixpoint bLtohS_tail (bl : bL)(hSLen : nat)(acc : string) : string :=
  match hSLen with
  | O => acc
  | S len' =>
  let (pre, suf) := partListBack bl 4 in
    match suf with
    | [] => acc
    | _ => bLtohS_tail pre len' ((NtohChar (bLtoN suf)) ++ acc)
    end
  end.

Definition bLtohS (bl : bL) : string :=
  bLtohS_tail bl (Nat.div (Nat.add (length bl) 3%nat) 4%nat) "".

Definition bStohS (m_bin : string) : string :=
  bLtohS (bStobL m_bin). 

Fixpoint strtobL_tail (s : string)(acc : bL) :=
  match s with
  | "" => acc
  | String c tl =>
      strtobL_tail tl (List.app acc (NtobL_len 8 (N_of_ascii c)))
  end. 

Definition strtobL (s : string) :=
  strtobL_tail s [].

Fixpoint BL2str_tail (Bl : BL)(acc : string) :=
  match Bl with
  | [] => acc
  | h :: tl =>
      BL2str_tail tl (acc ++ (String (ascii_of_N (Byte.to_N h)) ""))
  end. 
 
Definition BL2str (Bl : BL) :=
  BL2str_tail Bl "". 

Definition bLtostr (bl : bL) := 
  BL2str (bLtoBL bl). 


Fixpoint bLeqb (bl1 bl2 : bL) : bool :=
  match bl1, bl2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => 
      if Bool.eqb h1 h2 then bLeqb t1 t2
        else false
  | _, _ => false
  end. 

Fixpoint All0bL (bl : bL) : bool :=
  match bl with
  | [] => true
  | true :: tl => false
  | false :: tl =>
      All0bL tl
  end. 

Fixpoint bLXOR_tail (a b acc : bL) : bL :=
  match a, b with
  | ha :: ta, hb :: tb =>
       bLXOR_tail ta tb ((xorb ha hb) :: acc)
  | [], _ => List.app (rev b) acc
  | _, [] => List.app (rev a) acc 
  end. 

(* a and b are aligned to the right and 
 keep the overhead to the left of the result *)
Definition bLXOR (a b : bL) :=
  (bLXOR_tail (rev a) (rev b) []).

(*
Compute bLXOR (bStobL "111") (bStobL "1"). 
Compute bLXOR (bStobL "110") (bStobL "1"). 
Compute bLXOR (bStobL "011") (bStobL "1"). 
Compute bLXOR (bStobL "11111101") (bStobL "111"). 
Compute bLXOR (bStobL "111") (bStobL "11111101"). 
Compute bLXOR (bStobL "111001") (bStobL "11111101"). 
*)

(*4.2.5*)
Inductive field_type : Set :=
  pri : field_type | ext : field_type .

(* Same as NtoBL *)
Definition Field2BL_p :=  NtoBL. 


Definition Field2BL_b (m : N) :=
  NtoBL_len (N.to_nat (div_ceil_N m 8)). 
 
(*4.2.6*)
Definition BL2Field_p (Bl : BL)(q : N) : option N :=
  (fun (alpha : N)  => if leb q alpha then None else Some alpha) (BLtoN Bl).  

Definition BL2Field_b (Bl : BL)(m : N) : option N :=
  BL2Field_p Bl (N.shiftl 1 m). 

(*
Definition BL2Field_b (Bl : BL) : bL :=
  BLtobL Bl. 
*)

(*4.2.7*)
(* Still no need to convert since we are using N *)
(*
Definition FieldtoN_m (alpha : bL) : N :=
  bLtoN alpha. 
  *)

Close Scope list_scope. 
