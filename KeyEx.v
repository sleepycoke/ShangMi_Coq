Require Export Signature. 


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

(* K = k || Ha! *)
Fixpoint Computek (HaList' : list bL)(acc : bL) : bL :=
  match HaList' with
  | [] => acc
  | h :: tl => Computek tl (acc ++ h)
  end. 

Definition KDF (Z : bL)(klen : nat)(hash_v : bL -> bL)(v : nat) : bL :=
  let HaList := ComputeHaList ((div_ceil_nat klen v) - 1) 1 Z hash_v [] in
  match HaList with
  | [] => [] (*HaList should not be empty *)
  | HaLast :: tl =>
    let HaiEx := 
      if Nat.eqb (Nat.modulo klen v) 0 then HaLast
      else subList 0 (klen - v * (Nat.div klen v)) HaLast in
      (Computek tl []) ++ HaiEx
  end. 

(* A1 - A3 *)
Definition ComputeR (ml : GE -> N -> GE)(G : GE)(r : N) : GE :=
  ml G r. 

Definition ComputeTide (w x : N) : N :=
      let w2 := N.shiftl 1 w in
      w2 + (N.land x (w2 - 1) ). 

Definition ComputeW (n : N) : N :=
  (div_ceil_N (N.size (n - 1)) 2) - 1.

(*B1 - B9*)
Definition ComputeV (ml : GE -> N -> GE)(ad : GE -> GE -> GE)(n h t x_tide  : N)(P R : GE): GE :=
  ml (ad P (ml R x_tide)) (P_mul n h t). 
Definition ComputeK (m : N)(hash_v : bL -> bL)(v : nat)(klen : nat)
  (x y : N)(ZA ZB : bL) : bL :=
  let n2bl := if m =? 0 then N2BbL else N2BbL_len (N.to_nat m) in
  KDF ((n2bl x) ++ (n2bl y) ++ ZA ++ ZB) klen hash_v v. 
Definition ComputeS (m : N)(hash_v : bL -> bL)(prehS : string)(ZA ZB : bL)(x y x1 y1 x2 y2 : N) : bL :=
  let n2bl := if m =? 0 then N2BbL else N2BbL_len (N.to_nat m) in
    hash_v ((hS2bL prehS) ++ (n2bl y) ++ (hash_v ((n2bl x) ++ ZA ++ ZB ++ (n2bl x1) ++ (n2bl y1) ++ (n2bl x2) ++ (n2bl y2)))). 

(* A5 *)
Definition ComputeT (n d x_tide r : N) : N := P_add n d (x_tide * r). 
Definition ComputeRBKBSB (hash_v : bL -> bL)(v : nat)(klen : nat)(comk : (bL -> bL) -> nat ->nat -> N -> N -> bL -> bL -> bL)(coms : (bL -> bL) -> string -> bL -> bL -> N -> N -> N -> N -> N -> N -> bL)(ml : GE -> N -> GE)(ad : GE -> GE -> GE)(OnCrv : N -> N -> bool)
  (G : GE)(n h : N)(ZA ZB : bL)(RA PA : GE)(rB dB : N): optErr (GE * bL * bL) :=
  let RB := ComputeR ml G rB in 
  match RB with
  | InfO => Error "RB = InfO" (* impossible since rB < n *)
  | Cop (x2, y2) =>
      (* w2 := 2^w < n by definiton of w *)
      let w := ComputeW n in
      let x2_tide := ComputeTide w x2 in
      let tB := ComputeT n dB x2_tide rB in
      (* B5 *)
      match RA with
      | InfO => Error "RA = InfO"
      | Cop (x1, y1) => if negb (OnCrv x1 y1) then Error "RA is not on the curve" else 
        let x1_tide := ComputeTide w x1 in
        (* B6 *)
        let V := ComputeV ml ad n h tB x1_tide PA RA in
        match V with
        | InfO => Error "V = InfO"
        | Cop (xV, yV) =>
            (* B7 *)
            let KB := comk hash_v v klen xV yV ZA ZB in
            (* B8 *)
            let SB := coms hash_v "02" ZA ZB xV yV x1 y1 x2 y2 in
            Normal (RB, KB, SB)
        end
      end
  end.

Definition ComputeRBKBSB_pf (hash_v : bL -> bL)(v : nat)(klen : nat)
  (p a b : N)(G : GE)(n h : N)(ZA ZB : bL)(RA PA : GE)(rB dB : N)
  : optErr (GE * bL * bL) :=
  ComputeRBKBSB hash_v v klen (ComputeK 0) (ComputeS 0) (pf_mul p a) (pf_add p a) (OnCurve_pf p a b)
    G n h ZA ZB RA PA rB dB . 

Definition ComputeRBKBSB_bfp (hash_v : bL -> bL)(v : nat)(klen : nat)(m gp a b : N) (G : GE)(n h : N)(ZA ZB : bL)(RA PA : GE)(rB dB : N): optErr (GE * bL * bL) :=
  ComputeRBKBSB hash_v v klen (ComputeK m) (ComputeS m) (bfp_mul m gp a) (bfp_add m gp a) (OnCurve_bfp gp a b) G n h ZA ZB RA PA rB dB. 

(* A4-A10 *)
Definition ComputeKAS1SA (hash_v : bL -> bL)(v : nat)(klen : nat)(comk : (bL -> bL) -> nat ->nat -> N -> N -> bL -> bL -> bL)(coms : (bL -> bL) -> string -> bL -> bL -> N -> N -> N -> N -> N -> N -> bL)(ml : GE -> N -> GE)(ad : GE -> GE -> GE)(OnCrv : N -> N -> bool)
(rA dA n h : N) (PB RA RB : GE)(ZA ZB SB : bL): optErr (bL * bL * bL) :=
  match RA with
  | InfO => Error "RA = InfO"
  | Cop (x1, y1) =>
      let w := ComputeW n in
      let x1_tide := ComputeTide w x1 in
      let tA := ComputeT n dA x1_tide rA in
      match RB with
      | InfO => Error "RB = InfO" (*RB cannot be InfO since rB < n*)
      | Cop (x2, y2) =>
        if negb (OnCrv x2 y2) then Error "RB is not on curve"
        else let x2_tide := ComputeTide w x2 in
        let U := ComputeV ml ad n h tA x2_tide PB RB in  
        match U with
        | InfO => Error "U = InfO"
        | Cop (xU, yU) =>
            let KA := comk hash_v v klen xU yU ZA ZB in
            let S1 := coms hash_v "02" ZA ZB xU yU x1 y1 x2 y2 in
            if negb (bLeqb S1 SB) then Error "S1 != SB"
            else let SA := coms hash_v "03" ZA ZB xU yU x1 y1 x2 y2 in
              Normal (KA, S1, SA)
        end
      end
  end. 

Definition ComputeKAS1SA_pf (hash_v : bL -> bL)(v : nat)(klen : nat)(p a b : N) (rA dA n h : N) (PB RA RB : GE)(ZA ZB SB : bL): optErr (bL * bL * bL) :=
  ComputeKAS1SA  hash_v v klen (ComputeK 0) (ComputeS 0) (pf_mul p a) (pf_add p a) (OnCurve_pf p a b)
rA dA n h PB RA RB ZA ZB SB. 

Definition ComputeKAS1SA_bfp (hash_v : bL -> bL)(v : nat)(klen : nat)(m gp a b : N) (rA dA n h : N) (PB RA RB : GE)(ZA ZB SB : bL): optErr (bL * bL * bL) :=
  ComputeKAS1SA hash_v v klen (ComputeK m) (ComputeS m) (bfp_mul m gp a) (bfp_add m gp a) (OnCurve_bfp gp a b)
rA dA n h PB RA RB ZA ZB SB. 

(* B10 *)
Definition VeriS2eqSA (hash_v : bL -> bL)(coms : (bL -> bL) -> string -> bL -> bL -> N -> N -> N -> N -> N -> N -> bL)(ZA ZB SA: bL)(xV yV x1 y1 x2 y2 : N) : bool :=
  let S2 := coms hash_v "03" ZA ZB xV yV x1 y1 x2 y2 in
    bLeqb S2 SA. 
Definition VeriS2eqSA_pf (hash_v : bL -> bL)(ZA ZB SA: bL)(xV yV x1 y1 x2 y2 : N) : bool :=
  VeriS2eqSA hash_v (ComputeS 0) ZA ZB SA xV yV x1 y1 x2 y2. 

(*
Module test_pf. 
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
Definition x1bL := hS2bL "6CB56338 16F4DD56 0B1DEC45 8310CBCC 6856C095 05324A6D 23150C40 8F162BF0". 
Definition x1 := hS2N"6CB56338 16F4DD56 0B1DEC45 8310CBCC 6856C095 05324A6D 23150C40 8F162BF0". 
Definition y1bL := hS2bL "0D6FCF62 F1036C0A 1B6DACCF 57399223 A65F7D7B F2D9637E 5BBBEB85 7961BF1A". 
Definition y1 := hS2N"0D6FCF62 F1036C0A 1B6DACCF 57399223 A65F7D7B F2D9637E 5BBBEB85 7961BF1A". 

(*Time Compute ComputeR G rA p a.
Compute (x1, y1). Correct *)

(* Test of B1-B9 *)

Definition rB := hS2N "33FE2194 0342161C 55619C4A 0C060293 D543C80A F19748CE 176D8347 7DE71C80". 
Definition x2bL := hS2bL "1799B2A2 C7782953 00D9A232 5C686129 B8F2B533 7B3DCF45 14E8BBC1 9D900EE5".
Definition x2 := hS2N "1799B2A2 C7782953 00D9A232 5C686129 B8F2B533 7B3DCF45 14E8BBC1 9D900EE5".
Definition y2bL := hS2bL "54C9288C 82733EFD F7808AE7 F27D0E73 2F7C73A7 D9AC98B7 D8740A91 D0DB3CF4". 
Definition y2 := hS2N "54C9288C 82733EFD F7808AE7 F27D0E73 2F7C73A7 D9AC98B7 D8740A91 D0DB3CF4". 

(* Time Compute ComputeR G r p a.       
Compute (x2, y2). Correct *)

(*Compute N2hS (ComputeTide w x2 p). Correct*)
Definition x2_tide := hS2N "B8F2B533 7B3DCF45 14E8BBC1 9D900EE5".
Definition tB := hS2N "2B2E11CB F03641FC 3D939262 FC0B652A 70ACAA25 B5369AD3 8B375C02 65490C9F". 
(*Compute N2hS (P_add dB (x2_tide * rB) n).  Correct *)

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
Definition xV := bL2N xVbL. 
Definition yV := bL2N yVbL. 
Definition V := Cop (xV, yV). 
(*
Compute V. 
Time Compute pf_mul RA1 (h * tB) p a. Correct *)

Definition Z := xVbL ++ yVbL ++ ZA ++ ZB. 
Definition Z_short := (N2bL xV) ++ (N2bL yV) ++ ZA ++ ZB. 
Definition klen := 128%nat. 
 
Definition KB := hS2bL "55B0AC62 A6B927BA 23703832 C853DED4". 
(* Compute bL2hS (KDF Z klen Hash constant_v). (*Correct*) *)
(* Compute bL2hS (KDF Z_short klen Hash constant_v). (*Incorrect*) *)

Definition SB := hS2bL "284C8F19 8F141B50 2E81250F 1581C7E9 EEB4CA69 90F9E02D F388B454 71F5BC5C". 

(* Compute bL2hS (ComputeS "02" ZA ZB xV yV x1 y1 x2 y2 Hash). (*Correct*) *)

(*
Compute bL2hS (Hash(hS2bL "02" ++ (N2hbL yV) ++
  (Hash((N2hbL xV) ++ ZA ++ ZB ++ (N2hbL x1) ++ (N2hbL y1) 
    ++ (N2hbL x2) ++ (N2hbL y2))))). (* Incorrect *)

Compute bL2hS (Hash(hS2bL "02" ++ (yVbL) ++
  (Hash((xVbL) ++ ZA ++ ZB ++ (N2hbL x1) ++ (y1bL) 
    ++ (N2hbL x2) ++ (N2hbL y2))))). (* Correct So we need to convert into BL*)


Compute bL2hS (Hash(hS2bL "02" ++ (yVbL) ++
  (Hash((xVbL) ++ ZA ++ ZB ++ (N2BbL x1) ++ (N2BbL y1)
    ++ (N2BbL x2) ++ (N2BbL y2))))). (* Correct So we need to convert into BL*)
*)
(*Compute (RB, bL2hS KB, bL2hS SB). *)
(*
Time Compute  
  match ComputeRBKBSB_pf Hash constant_v klen p a b G n h ZA ZB RA PA rB dB with
  | Normal (r, k, s) =>
      Normal (r, bL2hS k, bL2hS s)
  | Error str => Error str
  end.
*)
(*
= Normal
         (Cop
            (10674756017693886118013130470205571129066026050907705581236911766144132583141,
            38349695398999244294516177264660271811914762859380595053573598523959505796340),
         "55b0ac62a6b927ba23703832c853ded4",
         "284c8f198f141b502e81250f1581c7e9eeb4ca6990f9e02df388b45471f5bc5c")
Finished transaction in 1479.333 secs (1475.634u,1.955s) (successful)
Correct *)
Definition KA := hS2bL "55B0AC62 A6B927BA 23703832 C853DED4". 
Definition S1 := hS2bL "284C8F19 8F141B50 2E81250F 1581C7E9 EEB4CA69 90F9E02D F388B454 71F5BC5C". 
Definition SA := hS2bL "23444DAF 8ED75343 66CB901C 84B3BDBB 63504F40 65C1116C 91A4C006 97E6CF7A". 

Definition result3 := ComputeKAS1SA_pf Hash constant_v klen p a b rA dA n h PB RA RB ZA ZB SB.  
(*
Time Compute match result3 with
| Error err => Error err
| Normal (ka, s1, sa) => Normal (bL2hS ka, bL2hS s1, bL2hS sa)
end. 
= Normal
         ("55b0ac62a6b927ba23703832c853ded4",
         "284c8f198f141b502e81250f1581c7e9eeb4ca6990f9e02df388b45471f5bc5c",
         "23444daf8ed7534366cb901c84b3bdbb63504f4065c1116c91a4c00697e6cf7a")
     : optErr (string * string * string)
Finished transaction in 919.87 secs (918.127u,0.839s) (successful)
Correct. 
*)
(*
Compute VeriS2eqSA ZA ZB SA xV yV x1 y1 x2 y2 Hash. 
* = true Correct. *)

Definition Z2 := hS2bL "00 83E628CF 701EE314 1E8873FE 55936ADF 24963F5D C9C64805 66C80F8A 1D8CC51B 01 524C647F 0C0412DE FD468BDA 3AE0E5A8 0FCC8F5C 990FEE11 60292923 2DCD9F36".
(*983BCF 106AB2DC C92F8AEA C6C60BF2 98BB0117*)
(*Compute bL2hS (KDF Z2 152 Hash constant_v).*) (*Correct*)

End test_pf. 
  *)


Module test_bfp. 
Definition m := 257%N. 
Definition gp := (N.shiftl 1 257) + (N.shiftl 1 12) + 1. 
Definition a := 0.
Definition b := hS2N "00 E78BCD09 746C2023 78A7E72B 12BCE002 66B9627E CB0B5A25 367AD1AD 4CC6242B". 
Definition h := 4%N. 

Definition n := hS2N "7FFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF BC972CF7 E6B6F900 945B3C6A 0CF6161D". 

Definition xG := hS2N "00 CDB9CA7F 1E6B0441 F658343F 4B10297C 0EF9B649 1082400A 62E7A748 5735FADD". 
Definition yG := hS2N "01 3DE74DA6 5951C4D7 6DC89220 D5F7777A 611B1C38 BAE260B1 75951DC8 060C2B3E". 
Definition G := Cop (xG, yG).
Definition dA := hS2N "4813903D 254F2C20 A94BC570 42384969 54BB5279 F861952E F2C5298E 84D2CEAA".
Definition xA := hS2N "00 8E3BDB2E 11F91933 88F1F901 CCC857BF 49CFC065 FB38B906 9CAAE6D5 AFC3592F". 
Definition yA := hS2N "00 4555122A AC0075F4 2E0A8BBD 2C0665C7 89120DF1 9D77B4E3 EE4712F5 98040415".
Definition PA := Cop (xA, yA).
Definition xB := hS2N "00 34297DD8 3AB14D5B 393B6712 F32B2F2E 938D4690 B095424B 89DA880C 52D4A7D9". 
Definition yB := hS2N "01 99BBF11A C95A0EA3 4BBD00CA 50B93EC2 4ACB6833 5D20BA5D CFE3B33B DBD2B62D". 
Definition PB := Cop (xB, yB).
Definition ZA := hS2bL "ECF00802 15977B2E 5D6D61B9 8A99442F 03E8803D C39E349F 8DCA5621 A9ACDF2B". 
Definition ZB := hS2bL "557BAD30 E183559A EEC3B225 6E1C7C11 F870D22B 165D015A CF9465B0 9B87B527". 
Definition rA := hS2N "54A3D667 3FF3A6BD 6B02EBB1 64C2A3AF 6D4A4906 229D9BFC E68CC366 A2E64BA4". 
Definition rB := hS2N "1F219333 87BEF781 D0A8F7FD 708C5AE0 A56EE3F4 23DBC2FE 5BDF6F06 8C53F7AD". 
Definition dB := hS2N "08F41BAE 0922F47C 212803FE 681AD52B 9BF28A35 E1CD0EC2 73A2CF81 3E8FD1DC". 
Definition klen := 128%nat. 
Definition RA' := bfp_mul m gp a G rA. 
Definition RB' := bfp_mul m gp a G rB. 
Definition x1 := hS2N "01 81076543 ED19058C 38B313D7 39921D46 B80094D9 61A13673 D4A5CF8C 7159E304".
Definition y1 := hS2N "01 D8CFFF7C A27A01A2 E88C1867 3748FDE9 A74C1F9B 45646ECA 0997293C 15C34DD8".
Definition RA := Cop (x1, y1). 
Definition x2 := hS2N "00 2A4832B4 DCD399BA AB3FFFE7 DD6CE6ED 68CC43FF A5F2623B 9BD04E46 8D322A2A".
Definition y2 := hS2N "00 16599BB5 2ED9EAFA D01CFA45 3CF3052E D60184D2 EECFD42B 52DB7411 0B984C23". 
Definition RB := Cop (x2, y2). 
Definition xV := hS2N "00 DADD0874 06221D65 7BC3FA79 FF329BB0 22E9CB7D DFCFCCFE 277BE8CD 4AE9B954".
Definition yV := hS2N "01 F0464B1E 81684E5E D6EF281B 55624EF4 6CAA3B2D 37484372 D91610B6 98252CC9". 
Definition SB := hS2bL "4EB47D28 AD3906D6 244D01E0 F6AEC73B 0B51DE15 74C13798 184E4833 DBAE295A". 
(*
Compute bL2hS (ComputeS_bf (N.to_nat m) "02" ZA ZB xV yV x1 y1 x2 y2 Hash). 
Correc. Same as SB *)
Definition xU := hS2N "00 DADD0874 06221D65 7BC3FA79 FF329BB0 22E9CB7D DFCFCCFE 277BE8CD 4AE9B954". 
Definition yU := hS2N "01 F0464B1E 81684E5E D6EF281B 55624EF4 6CAA3B2D 37484372 D91610B6 98252CC9". 
Definition KA := hS2bL "4E587E5C 66634F22 D973A7D9 8BF8BE23".
(*
Compute bL2hS (ComputeK m Hash constant_v klen xU yU ZA ZB). 
Correct Same as KA*)

(*
Time Compute match RA' with
  |InfO => ("", "")
  |Cop (x, y) => (N2hS x, N2hS y)
end. 
Time Compute match RB' with
  |InfO => ("", "")
  |Cop (x, y) => (N2hS x, N2hS y)
end. 
*)
(* Same as RA and RB *)
(*     = ("181076543ed19058c38b313d739921d46b80094d961a13673d4a5cf8c7159e304",
       "1d8cfff7ca27a01a2e88c18673748fde9a74c1f9b45646eca0997293c15c34dd8")
     : string * string
Finished transaction in 1172.412 secs (1168.732u,1.655s) (successful)
     = ("2a4832b4dcd399baab3fffe7dd6ce6ed68cc43ffa5f2623b9bd04e468d322a2a",
       "16599bb52ed9eafad01cfa453cf3052ed60184d2eecfd42b52db74110b984c23")
     : string * string
Finished transaction in 1156.16 secs (1155.32u,0.488s) (successful)
*)
(*
Time Compute match ComputeRBKBSB_bfp Hash constant_v klen m gp a b G n h ZA ZB RA PA rB dB with
| Error err => Error err
| Normal (rb, kb, sb) => Normal (
    match rb with
    | InfO => ("", "")
    | Cop (xrb, yrb) =>
        (N2hS xrb, N2hS yrb)
    end,
    bL2hS kb, bL2hS sb)
end. 
*)
(*= Normal
         ("2a4832b4dcd399baab3fffe7dd6ce6ed68cc43ffa5f2623b9bd04e468d322a2a",
         "16599bb52ed9eafad01cfa453cf3052ed60184d2eecfd42b52db74110b984c23",
         "4e587e5c66634f22d973a7d98bf8be23",
         "4eb47d28ad3906d6244d01e0f6aec73b0b51de1574c13798184e4833dbae295a")
     : optErr (string * string * string * string)
Finished transaction in 2817.141 secs (2815.495u,0.988s) (successful)
*)
(*Correct *)
(*
Time Compute match ComputeKAS1SA_bfp Hash constant_v klen m gp a b rA dA n h PB RA RB ZA ZB SB with
| Error err => Error err
| Normal (ka, s1, sa) => Normal (bL2hS ka, bL2hS s1, bL2hS sa)
end. 
*)
(*
*      = Normal
         ("4e587e5c66634f22d973a7d98bf8be23",
         "4eb47d28ad3906d6244d01e0f6aec73b0b51de1574c13798184e4833dbae295a",
         "588aa67064f24dc27ccaa1fab7e27dff811d500ad7ef2fb8f69ddf48cc0fecb7")
     : optErr (string * string * string)
Finished transaction in 1691.229 secs (1686.318u,1.809s) (successful)
Correct *)

End test_bfp. 

