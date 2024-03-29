Require Import KeyEx.
Open Scope ecfield_scope. 
Section test_pf. 
Definition A2_begin_description := "Example A.2 on SM2p3 Annex A, page 11, begins. ". 
Print A2_begin_description. 
Definition p := hStoN 
  "8542D69E 4C044F18 E8B92435 BF6FF7DE 45728391 5C45517D 722EDB8B 08F1DFC3". 
Definition field := pf_builder p Logic.eq_refl.
Definition aN := hStoN
  "787968B4 FA32C3FD 2417842E 73BBFEFF 2F3C848B 6831D7E0 EC65228B 3937E498". 
Definition a := wrapper field aN .

Definition bN := hStoN
  "63E4C6D3 B23B0C84 9CF84241 484BFE48 F61D59A5 B16BA06E 6E12D1DA 27C5249A". 
Definition b := wrapper field bN .
Definition crv := @pf_curve _ field a b Logic.eq_refl.
Definition h := 1%N. 
Definition xGN := hStoN
  "421DEBD6 1B62EAB6 746434EB C3CC315E 32220B3B ADD50BDC 4C4E6C14 7FEDD43D". 
Definition xG := wrapper field xGN .
Definition yGN := hStoN
  "0680512B CBB42C07 D47349D2 153B70C4 E5D7FDFC BFA36EA1 A85841B9 E46E09A2". 
Definition yG := wrapper field yGN .

Definition G := Cop field (xG, yG). 

Definition n := hStoN
  "8542D69E 4C044F18 E8B92435 BF6FF7DD 29772063 0485628D 5AE74EE7 C32E79B7". 
Definition w := ComputeW n.
Example wis127 : w = 127%N := Logic.eq_refl. 
Definition dAN := hStoN
  "6FCBA2EF 9AE0AB90 2BC3BDE3 FF915D44 BA4CC78F 88E2F8E7 F8996D3B 8CCEEDEE". 
Definition dA := wrapper field dAN.
Definition xAN := hStoN
  "3099093B F3C137D8 FCBBCDF4 A2AE50F3 B0F216C3 122D7942 5FE03A45 DBFE1655". 
Definition xA := wrapper field xAN.
Definition yAN := hStoN
  "3DF79E8D AC1CF0EC BAA2F2B4 9D51A4B3 87F2EFAF 48233908 6A27A8E0 5BAED98B". 
Definition yA := wrapper field yAN.
Definition dBN := hStoN
  "5E35D7D3 F3C54DBA C72E6181 9E730B01 9A84208C A3A35E4C 2E353DFC CB2A3B53". 
Definition dB := wrapper field dBN.
Definition xBN := hStoN
  "245493D4 46C38D8C C0F11837 4690E7DF 633A8A4B FB3329B5 ECE604B2 B4F37F43". 
Definition xB := wrapper field xBN.
Definition yBN := hStoN
  "53C0869F 4B9E1777 3DE68FEC 45E14904 E0DEA45B F6CECF99 18C85EA0 47C60A4C". 
Definition yB := wrapper field yBN.
Definition ZA := hStobL 
  "E4D1D0C3 CA4C7F11 BC8FF8CB 3F4C02A7 8F108FA0 98E51A66 8487240F 75E20F31". 
Definition ZB := hStobL 
  "6B4B6D0E 276691BD 4A11BF72 F4FB501A E309FDAC B72FA6CC 336E6656 119ABD67". 

(*Test of A1-A3*)
Definition rA := hStoN
  "83A2C9C8 B96E5AF7 0BD480B4 72409A9A 327257F1 EBB73F5B 073354B2 48668563". 
Definition x1bL := hStobL 
  "6CB56338 16F4DD56 0B1DEC45 8310CBCC 6856C095 05324A6D 23150C40 8F162BF0". 
Definition x1N := bLtoN x1bL. 
Definition x1 := wrapper field x1N. 
Definition y1bL := hStobL 
  "0D6FCF62 F1036C0A 1B6DACCF 57399223 A65F7D7B F2D9637E 5BBBEB85 7961BF1A". 
Definition y1N := bLtoN y1bL. 
Definition y1 := wrapper field y1N. 

(* Test of B1-B9 *)

Definition rB := hStoN 
  "33FE2194 0342161C 55619C4A 0C060293 D543C80A F19748CE 176D8347 7DE71C80". 
Definition x2bL := hStobL 
  "1799B2A2 C7782953 00D9A232 5C686129 B8F2B533 7B3DCF45 14E8BBC1 9D900EE5".
Definition x2N := hStoN 
  "1799B2A2 C7782953 00D9A232 5C686129 B8F2B533 7B3DCF45 14E8BBC1 9D900EE5".
Definition y2bL := hStobL 
  "54C9288C 82733EFD F7808AE7 F27D0E73 2F7C73A7 D9AC98B7 D8740A91 D0DB3CF4". 
Definition y2N := hStoN 
  "54C9288C 82733EFD F7808AE7 F27D0E73 2F7C73A7 D9AC98B7 D8740A91 D0DB3CF4". 
Definition x2 := wrapper field x2N.
Definition y2 := wrapper field y2N.

Definition x2_tilde := hStoN "B8F2B533 7B3DCF45 14E8BBC1 9D900EE5".

Example x2_tilde_test : x2_tilde = ComputeTilde field w x2.
Proof. vm_compute. reflexivity. Qed.   
Definition tB := hStoN 
  "2B2E11CB F03641FC 3D939262 FC0B652A 70ACAA25 B5369AD3 8B375C02 65490C9F". 
Example tB_test : tB 
  = ComputeT n (unwrapper field dB) x2_tilde rB := Logic.eq_refl. 

Definition x1_tilde := hStoN "E856C095 05324A6D 23150C40 8F162BF0". 
Example x1_tilde_test : x1_tilde = ComputeTilde field w x1.
Proof. vm_compute. reflexivity. Qed.   
Definition RA := Cop field (x1, y1). 
Example ra_test : GE_eqb RA (ComputeR crv G rA) = true. 
Proof. Time vm_compute. reflexivity. Qed.   (* 34s *)

Definition RB := Cop field (x2, y2). 
Example rb_test : GE_eqb RB (ComputeR crv G rB) = true. 
Proof. Time vm_compute. reflexivity. Qed.   (* 34s *)

Definition PA := Cop field (xA, yA). 
Definition PB := Cop field (xB, yB). 

Definition xA0 := hStoN 
  "2079015F 1A2A3C13 2B67CA90 75BB2803 1D6F2239 8DD8331E 72529555 204B495B".
Definition yA0 := hStoN 
  "6B3FE6FB 0F5D5664 DCA16128 B5E7FCFD AFA5456C 1E5A914D 1300DB61 F37888ED". 
Definition xA1 := hStoN 
  "1C006A3B FF97C651 B7F70D0D E0FC09D2 3AA2BE7A 8E9FF7DA F32673B4 16349B92".
Definition yA1 := hStoN 
  "5DC74F8A CC114FC6 F1A75CB2 86864F34 7F9B2CF2 9326A270 79B7D37A FC1C145B".
Definition xVbL := hStobL 
  "47C82653 4DC2F6F1 FBF28728 DD658F21 E174F481 79ACEF29 00F8B7F5 66E40905". 
Definition yVbL := hStobL 
  "2AF86EFE 732CF12A D0E09A1F 2556CC65 0D9CCCE3 E249866B BB5C6846 A4C4A295". 
Definition xVN := bLtoN xVbL. 
Definition yVN := bLtoN yVbL. 
Definition xV := wrapper field xVN. 
Definition yV := wrapper field yVN. 
Definition V := Cop field (xV, yV). 
Example Vtest : GE_eqb (ComputeV (pf_mul a) (pf_add a) n h tB x1_tilde PA RA)
  V = true.
Proof. Time vm_compute. reflexivity. Qed. (* 52.815 secs *)

Definition Z := hStobL "47C82653 4DC2F6F1 FBF28728 DD658F21 E174F481 79ACEF29
 00F8B7F5 66E40905 2AF86EFE 732CF12A D0E09A1F 2556CC65 0D9CCCE3 E249866B 
 BB5C6846 A4C4A295 E4D1D0C3 CA4C7F11 BC8FF8CB 3F4C02A7 8F108FA0 98E51A66 
 8487240F 75E20F31 6B4B6D0E 276691BD 4A11BF72 F4FB501A E309FDAC B72FA6CC 
 336E6656 119ABD67". 
Example Ztest : Z = xVbL ++ yVbL ++ ZA ++ ZB. 
Proof. reflexivity. Qed. 

Definition klen := 128%nat. 
 
Definition KB := 
  hStobL "55B0AC62 A6B927BA 23703832 C853DED4". 
Example KBtest : KB = KDF SM3_Hash constant_v klen  Z. 
Proof. vm_compute. reflexivity. Qed. 

Definition SB := hStobL 
  "284C8F19 8F141B50 2E81250F 1581C7E9 EEB4CA69 90F9E02D F388B454 71F5BC5C". 

Example SBtest : SB = @ComputeS _ field SM3_Hash "02" ZA ZB xV yV x1 y1 x2 y2.
Proof. vm_compute. reflexivity. Qed. 

Example rbkbsb_test : 
  match ComputeRBKBSB SM3_Hash constant_v klen crv field 
    G n h ZA ZB RA PA rB dBN with  
  | Error str => Error str
  | Normal (r, k, s) => Normal (GE_uwp r, k, s)
  end = Normal (GE_uwp RB, KB, SB).
Proof. Time vm_compute. reflexivity. Qed. 
(*94.608 secs*)

Definition KA := hStobL "55B0AC62 A6B927BA 23703832 C853DED4". 
Definition S1 := hStobL 
  "284C8F19 8F141B50 2E81250F 1581C7E9 EEB4CA69 90F9E02D F388B454 71F5BC5C". 
Definition SA := hStobL 
  "23444DAF 8ED75343 66CB901C 84B3BDBB 63504F40 65C1116C 91A4C006 97E6CF7A". 

Example kas1sa_test : Normal (KA, S1, SA) = ComputeKAS1SA SM3_Hash constant_v
 klen crv field rA dAN n h PB RA RB ZA ZB SB.  
Proof. Time vm_compute. reflexivity. Qed. 
(* 67.986 secs *)
Example veris2eqsa_test : @VeriS2eqSA _ field SM3_Hash ZA ZB SA xV yV x1 y1 x2 y2 = true.
Proof. Time vm_compute. reflexivity. Qed.  
(*5.392 secs *)
Definition A2_end_description := "Example A.2 on SM2p3 Annex A, page 11, ended. ". 
Print A2_end_description. 
End test_pf. 


(*Module test_bfp. 
Definition m := 257%N. 
Definition gp := (N.shiftl 1 257) + (N.shiftl 1 12) + 1. 
Definition a := 0.
Definition b := hStoN "00 E78BCD09 746C2023 78A7E72B 
  12BCE002 66B9627E CB0B5A25 367AD1AD 4CC6242B". 
Definition h := 4%N. 

Definition n := hStoN "7FFFFFFF FFFFFFFF FFFFFFFF 
  FFFFFFFF BC972CF7 E6B6F900 945B3C6A 0CF6161D". 

Definition xG := hStoN "00 CDB9CA7F 1E6B0441 F658343F 
  4B10297C 0EF9B649 1082400A 62E7A748 5735FADD". 
Definition yG := hStoN "01 3DE74DA6 5951C4D7 6DC89220 
  D5F7777A 611B1C38 BAE260B1 75951DC8 060C2B3E". 
Definition G := Cop (xG, yG).
Definition dA := hStoN "4813903D 254F2C20 A94BC570 
  42384969 54BB5279 F861952E F2C5298E 84D2CEAA".
Definition xA := hStoN "00 8E3BDB2E 11F91933 88F1F901 
  CCC857BF 49CFC065 FB38B906 9CAAE6D5 AFC3592F". 
Definition yA := hStoN "00 4555122A AC0075F4 2E0A8BBD 
  2C0665C7 89120DF1 9D77B4E3 EE4712F5 98040415".
Definition PA := Cop (xA, yA).
Definition xB := hStoN "00 34297DD8 3AB14D5B 393B6712 
  F32B2F2E 938D4690 B095424B 89DA880C 52D4A7D9". 
Definition yB := hStoN "01 99BBF11A C95A0EA3 4BBD00CA 
  50B93EC2 4ACB6833 5D20BA5D CFE3B33B DBD2B62D". 
Definition PB := Cop (xB, yB).
Definition ZA := hStobL "ECF00802 15977B2E 5D6D61B9 
  8A99442F 03E8803D C39E349F 8DCA5621 A9ACDF2B". 
Definition ZB := hStobL "557BAD30 E183559A EEC3B225 
  6E1C7C11 F870D22B 165D015A CF9465B0 9B87B527". 
Definition rA := hStoN "54A3D667 3FF3A6BD 6B02EBB1 
  64C2A3AF 6D4A4906 229D9BFC E68CC366 A2E64BA4". 
Definition rB := hStoN "1F219333 87BEF781 D0A8F7FD 
  708C5AE0 A56EE3F4 23DBC2FE 5BDF6F06 8C53F7AD". 
Definition dB := hStoN "08F41BAE 0922F47C 212803FE 
  681AD52B 9BF28A35 E1CD0EC2 73A2CF81 3E8FD1DC". 
Definition klen := 128%nat. 
Definition RA' := bfp_mul m gp a G rA. 
Definition RB' := bfp_mul m gp a G rB. 
Definition x1 := hStoN "01 81076543 ED19058C 38B313D7
  39921D46 B80094D9 61A13673 D4A5CF8C 7159E304".
Definition y1 := hStoN "01 D8CFFF7C A27A01A2 E88C1867
  3748FDE9 A74C1F9B 45646ECA 0997293C 15C34DD8".
Definition RA := Cop (x1, y1). 
Definition x2 := hStoN "00 2A4832B4 DCD399BA AB3FFFE7
  DD6CE6ED 68CC43FF A5F2623B 9BD04E46 8D322A2A".
Definition y2 := hStoN "00 16599BB5 2ED9EAFA D01CFA45 
  3CF3052E D60184D2 EECFD42B 52DB7411 0B984C23". 
Definition RB := Cop (x2, y2). 
Definition xV := hStoN "00 DADD0874 06221D65 7BC3FA79
  FF329BB0 22E9CB7D DFCFCCFE 277BE8CD 4AE9B954".
Definition yV := hStoN "01 F0464B1E 81684E5E D6EF281B
  55624EF4 6CAA3B2D 37484372 D91610B6 98252CC9". 
Definition SB := hStobL "4EB47D28 AD3906D6 244D01E0 
  F6AEC73B 0B51DE15 74C13798 184E4833 DBAE295A". 
(*
Compute bLtohS (ComputeS_bf (N.to_nat m) "02" ZA ZB xV yV
 x1 y1 x2 y2 SM3_Hash). 
Correc. Same as SB *)
Definition xU := hStoN "00 DADD0874 06221D65 7BC3FA79 
  FF329BB0 22E9CB7D DFCFCCFE 277BE8CD 4AE9B954". 
Definition yU := hStoN "01 F0464B1E 81684E5E D6EF281B 
  55624EF4 6CAA3B2D 37484372 D91610B6 98252CC9". 
Definition KA := hStobL "4E587E5C 66634F22 D973A7D9 
  8BF8BE23".
(*
Compute bLtohS 
  (ComputeK m SM3_Hash constant_v klen xU yU ZA ZB). 
Correct Same as KA*)

(*
Time Compute match RA' with
  |InfO => ("", "")
  |Cop (x, y) => (NtohS x, NtohS y)
end. 
Time Compute match RB' with
  |InfO => ("", "")
  |Cop (x, y) => (NtohS x, NtohS y)
end. 
*)
(* Same as RA and RB *)
(*     = ("181076543ed19058c38b313d739921d46b80094d961a136
          73d4a5cf8c7159e304",
       "1d8cfff7ca27a01a2e88c18673748fde9a74c1f9b45646eca0
       997293c15c34dd8")
     : string * string
Finished transaction in 1172.412 secs (1168.732u,1.655s)
 (successful)
     = ("2a4832b4dcd399baab3fffe7dd6ce6ed68cc43ffa5f2623b9
         bd04e468d322a2a",
       "16599bb52ed9eafad01cfa453cf3052ed60184d2eecfd42b52
       db74110b984c23")
     : string * string
Finished transaction in 1156.16 secs (1155.32u,0.488s) 
(successful)
*)
(*
Time Compute match ComputeRBKBSB_bfp SM3_Hash constant_v klen 
  m gp a b G n h ZA ZB RA PA rB dB with
| Error err => Error err
| Normal (rb, kb, sb) => Normal (
    match rb with
    | InfO => ("", "")
    | Cop (xrb, yrb) =>
        (NtohS xrb, NtohS yrb)
    end,
    bLtohS kb, bLtohS sb)
end. 
*)
(*= Normal
         ("2a4832b4dcd399baab3fffe7dd6ce6ed68cc43ffa5f2623
          b9bd04e468d322a2a",
         "16599bb52ed9eafad01cfa453cf3052ed60184d2eecfd42b
          52db74110b984c23",
         "4e587e5c66634f22d973a7d98bf8be23",
         "4eb47d28ad3906d6244d01e0f6aec73b0b51de1574c13798
          184e4833dbae295a")
     : optErr (string * string * string * string)
Finished transaction in 2817.141 secs (2815.495u,0.988s) 
(successful)
*)
(*Correct *)
(*
Time Compute match ComputeKAS1SA_bfp SM3_Hash constant_v klen
 m gp a b rA dA n h PB RA RB ZA ZB SB with
| Error err => Error err
| Normal (ka, s1, sa) =>
   Normal (bLtohS ka, bLtohS s1, bLtohS sa)
end. 
*)
(*
*      = Normal
         ("4e587e5c66634f22d973a7d98bf8be23",
         "4eb47d28ad3906d6244d01e0f6aec73b0b51de1574c13798
          184e4833dbae295a",
         "588aa67064f24dc27ccaa1fab7e27dff811d500ad7ef2fb8
          f69ddf48cc0fecb7")
     : optErr (string * string * string)
Finished transaction in 1691.229 secs (1686.318u,1.809s) 
(successful)
Correct *)

End test_bfp. 
*)

