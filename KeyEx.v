Require Export Signature. 

Definition constant_v := 256%nat. (*According to the examples. *)

(* ceil(x/y) *)
Definition div_ceil_nat (x : nat)(y : nat) : nat :=
  Nat.div (x + y - 1%nat) y. 
Definition div_ceil_N (x : N)(y : N) : N :=
  N.div (x + y - 1%N) y. 

(*
Fixpoint f (n : N) :=
  match n with
  | 0 => 1
  | _ => f(pred n)
  end.   

Compute f 5. 
*)
(* TODO Should we imp a general hash_v here? ignored for now *)
(* j = ceil(klen/v) - i, from ceil(klen/v) - 1 to 0 *)
(* i from 1 to ceil(klen/v), ct = N2bL_len 32 i*)
(* TODO though klen/v could be as long as 2^32, I choose to use nat for 
 simplicity, which suffices for the tests, aka 128 klen *)
(* Returns a reversed HaList *)
(* hash_v returns a bL of length v *)
Fixpoint ComputeHaList (j : nat)(i : N)(Z : bL)(hash_v : bL -> bL)
  (acc : list bL){struct j} :=
  let HaList := hash_v (Z ++ (N2bL_len 32 i)) :: acc in
  match j with
  | O => HaList 
  | S j' => 
      ComputeHaList j' (i + 1) Z hash_v HaList
  end. 

(* K = K' || Ha! *)
Fixpoint ComputeK' (HaList' : list bL)(acc : bL) : bL :=
  match HaList' with
  | [] => acc
  | h :: tl => ComputeK' tl (acc ++ h)
  end. 

Definition KDF (Z : bL)(klen : nat)(hash_v : bL -> bL)(v : nat) : bL :=
  let HaList := ComputeHaList ((div_ceil_nat klen v) - 1) 1 Z hash_v [] in
  match HaList with
  | [] => [] (*HaList should not be empty *)
  | HaLast :: tl =>
    let HaiEx := 
      if Nat.eqb (Nat.modulo klen v) 0 then HaLast
      else subList 0 (klen - v * (Nat.div klen v)) HaLast in
      (ComputeK' tl []) ++ HaiEx
  end. 

(* A1 - A3 *)
Definition ComputeR (G : FEp)(r p a: N) : FEp :=
  pf_mul G r p a. 

Definition ComputeTide (w2 x p : N) : N :=
      F_add w2 (N.land x (w2 - 1) ) p. 

Definition ComputeW (n : N) : N :=
  (div_ceil_N (N.size (n - 1)) 2) - 1.

Check (bL * bL)%type. 
Check option nat. 
Check option. 
Print list. 
Print option.
Inductive optErr (A : Type) : Type :=
| Normal : A -> optErr A
| Error : string -> optErr A. 

Arguments Normal {A} _.
Arguments Error {A}.

Print optErr.
Check optErr. 

(*B1 - B9*)
Definition ComputeRBKBSB (rB a b p dB n h : N)(G RA PA : FEp)(ZA ZB : bL)(klen : nat)(hash_v : bL -> bL)(v : nat) : optErr (FEp * bL * bL) :=
  let RB := ComputeR G rB p a in 
  match RB with
  | InfO => Error "RB = InfO" (* impossible since rB < n *)
  | Cop (x2, y2) =>
      (* w2 := 2^w < n by definiton of w *)
      let w := ComputeW n in
      let w2 := N.shiftl 1 w in
      let x2_tide := ComputeTide w2 x2 p in
      let tB := F_add dB (x2_tide * rB) n in
      (* B5 *)
      match RA with
      | InfO => Error "RA = InfO"
      | Cop (x1, y1) => 
          if negb ((N.square y1) mod n =? ((power x1 3 n) + a * x1 + b) mod n) then Error "RA is not on the curve" else 
        let x1_tide := ComputeTide w2 x1 p in
        (* B6 *)
        match pf_mul (pf_add PA (pf_mul RA x1_tide p a) p a)
        (F_mul h tB n) p a with
        | InfO => Error "V = InfO"
        | Cop (xV, yV) =>
            (* B7 *)
            let KB := KDF ((N2bL xV) ++ (N2bL yV) ++ ZA ++ ZB) klen hash_v v in
            (* B8 *)
            let SB := hash_v 
              ((hS2bL "02") ++ (N2bL yV) ++ (hash_v (N2bL xV) ++ ZA ++ ZB ++ (N2bL x1) ++ (N2bL y1) ++ (N2bL x2) ++ (N2bL y2))) in
            Normal (RB, KB, SB)
        end
      end
  end.
             
Module test. 
Definition p := hS2N "8542D69E 4C044F18 E8B92435 BF6FF7DE 45728391 5C45517D 722EDB8B 08F1DFC3". 
Definition a := hS2N"787968B4 FA32C3FD 2417842E 73BBFEFF 2F3C848B 6831D7E0 EC65228B 3937E498". 
Definition b := hS2N"63E4C6D3 B23B0C84 9CF84241 484BFE48 F61D59A5 B16BA06E 6E12D1DA 27C5249A". 
Definition h := 1%N. 
Definition xG := hS2N"421DEBD6 1B62EAB6 746434EB C3CC315E 32220B3B ADD50BDC 4C4E6C14 7FEDD43D". 
Definition yG := hS2N"0680512B CBB42C07 D47349D2 153B70C4 E5D7FDFC BFA36EA1 A85841B9 E46E09A2". 

Definition G := Cop (xG, yG). 

Definition n := hS2N"8542D69E 4C044F18 E8B92435 BF6FF7DD 29772063 0485628D 5AE74EE7 C32E79B7". 
Definition dA := hS2N"6FCBA2EF 9AE0AB90 2BC3BDE3 FF915D44 BA4CC78F 88E2F8E7 F8996D3B 8CCEEDEE". 
Definition xA := hS2N"3099093B F3C137D8 FCBBCDF4 A2AE50F3 B0F216C3 122D7942 5FE03A45 DBFE1655". 
Definition yA := hS2N"3DF79E8D AC1CF0EC BAA2F2B4 9D51A4B3 87F2EFAF 48233908 6A27A8E0 5BAED98B". 
Definition dB := hS2N"5E35D7D3 F3C54DBA C72E6181 9E730B01 9A84208C A3A35E4C 2E353DFC CB2A3B53". 
Definition xB := hS2N"245493D4 46C38D8C C0F11837 4690E7DF 633A8A4B FB3329B5 ECE604B2 B4F37F43". 
Definition yB := hS2N"53C0869F 4B9E1777 3DE68FEC 45E14904 E0DEA45B F6CECF99 18C85EA0 47C60A4C". 
Definition ZA := hS2bL "E4D1D0C3 CA4C7F11 BC8FF8CB 3F4C02A7 8F108FA0 98E51A66 8487240F 75E20F31". 
Definition ZB := hS2bL "6B4B6D0E 276691BD 4A11BF72 F4FB501A E309FDAC B72FA6CC 336E6656 119ABD67". 

(*Test of A1-A3*)
Definition rA := hS2N"83A2C9C8 B96E5AF7 0BD480B4 72409A9A 327257F1 EBB73F5B 073354B2 48668563". 
Definition x1 := hS2N"6CB56338 16F4DD56 0B1DEC45 8310CBCC 6856C095 05324A6D 23150C40 8F162BF0". 
Definition y1 := hS2N"0D6FCF62 F1036C0A 1B6DACCF 57399223 A65F7D7B F2D9637E 5BBBEB85 7961BF1A". 

(*Time Compute ComputeR G rA p a.
Compute (x1, y1). Correct *)

(* Test of B1-B9 *)

Definition rB := hS2N "33FE2194 0342161C 55619C4A 0C060293 D543C80A F19748CE 176D8347 7DE71C80". 
Definition x2 := hS2N "1799B2A2 C7782953 00D9A232 5C686129 B8F2B533 7B3DCF45 14E8BBC1 9D900EE5".
Definition y2 := hS2N "54C9288C 82733EFD F7808AE7 F27D0E73 2F7C73A7 D9AC98B7 D8740A91 D0DB3CF4". 

(* Time Compute ComputeR G r p a.       
Compute (x2, y2). Correct *)

Definition w2 := N.shiftl 1 127.

(*Compute N2hS (ComputeTide w2 x2 p). Correct*)
Definition x2_tide := hS2N "B8F2B533 7B3DCF45 14E8BBC1 9D900EE5".
Definition tB := hS2N "2B2E11CB F03641FC 3D939262 FC0B652A 70ACAA25 B5369AD3 8B375C02 65490C9F". 
(*Compute N2hS (F_add dB (x2_tide * rB) n).  Correct *)

(* Compute ComputeW n. Correct should be 127*)
Definition x1_tide := hS2N "E856C095 05324A6D 23150C40 8F162BF0". 
(*Compute N2hS (ComputeTide w2 x1 p). Correct *) 
Definition RA := Cop (x1, y1). 
Definition RB := Cop (x2, y2). 
Definition PA := Cop (xA, yA). 
Definition PB := Cop (xB, yB). 
Definition xA0 := hS2N "2079015F 1A2A3C13 2B67CA90 75BB2803 1D6F2239 8DD8331E 72529555 204B495B".
Definition yA0 := hS2N "6B3FE6FB 0F5D5664 DCA16128 B5E7FCFD AFA5456C 1E5A914D 1300DB61 F37888ED". 
(*Compute Cop (xA0, yA0). 
Time Compute ComputeR RA x1_tide p a. Correct *)
Definition RA0 := Cop (xA0, yA0). 
Definition xA1 := hS2N "1C006A3B FF97C651 B7F70D0D E0FC09D2 3AA2BE7A 8E9FF7DA F32673B4 16349B92".
Definition yA1 := hS2N "5DC74F8A CC114FC6 F1A75CB2 86864F34 7F9B2CF2 9326A270 79B7D37A FC1C145B".
Definition RA1 := Cop (xA1, yA1). 
(*
Compute RA1.
Compute pf_add PA RA0 p a. Correct *)
Definition xVbL := hS2bL "47C82653 4DC2F6F1 FBF28728 DD658F21 E174F481 79ACEF29 00F8B7F5 66E40905". 
Definition yVbL := hS2bL "2AF86EFE 732CF12A D0E09A1F 2556CC65 0D9CCCE3 E249866B BB5C6846 A4C4A295". 
Definition V := Cop (bL2N xVbL, bL2N yVbL). 
(*
Compute V. 
Time Compute pf_mul RA1 (h * tB) p a. Correct *)

Definition Z := xVbL ++ yVbL ++ ZA ++ ZB. 
Definition klen := 128%nat. 
 
Definition KB := hS2bL "55B0AC62 A6B927BA 23703832 C853DED4". 
(*Compute bL2hS (KDF Z klen Hash constant_v).*) (*Correct*)

Check ComputeRBKBSB rB a b p dB n h G RA PA ZA ZB klen Hash constant_v. 
Definition SB := hS2bL "284C8F19 8F141B50 2E81250F 1581C7E9 EEB4CA69 90F9E02D F388B454 71F5BC5C". 
Compute (RB, bL2hS KB, bL2hS SB). 


Time Check 
  match ComputeRBKBSB rB a b p dB n h G RA PA ZA ZB klen Hash constant_v with
  | Normal (r, k, s) =>
      Normal (r, bL2hS k, bL2hS s)
  | Error str => Error str
  end. 




Definition Z2 := hS2bL "00 83E628CF 701EE314 1E8873FE 55936ADF 24963F5D C9C64805 66C80F8A 1D8CC51B 01 524C647F 0C0412DE FD468BDA 3AE0E5A8 0FCC8F5C 990FEE11 60292923 2DCD9F36".
(*983BCF 106AB2DC C92F8AEA C6C60BF2 98BB0117*)
(*Compute bL2hS (KDF Z2 152 Hash constant_v).*) (*Correct*)

End test. 

