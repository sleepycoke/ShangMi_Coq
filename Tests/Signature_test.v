Require Import Signature. 
Section A_1. 
Definition IDa := hStobL "414C 49434531 32334059 41484F4F 2E434F4D".
Definition ENTLa := hStobL "0090". 
(*
Compute IDa. 
Compute bLtohS (ENTL IDa).  

Compute bLtobS ENTLa. 
*)

Definition pbL := hStobL 
"8542D69E 4C044F18 E8B92435 BF6FF7DE 45728391 5C45517D 722EDB8B 08F1DFC3".
Definition p := bLtoN pbL. 
Definition abL := hStobL
  "787968B4 FA32C3FD 2417842E 73BBFEFF 2F3C848B 6831D7E0 EC65228B 3937E498".
Definition a := bLtoN abL.
Definition bbL := hStobL
  "63E4C6D3 B23B0C84 9CF84241 484BFE48 F61D59A5 B16BA06E 6E12D1DA 27C5249A". 
Definition b := bLtoN bbL.
Definition xGbL := hStobL
  "421DEBD6 1B62EAB6 746434EB C3CC315E 32220B3B ADD50BDC 4C4E6C14 7FEDD43D".
Definition xG := bLtoN xGbL.
Definition yGbL := hStobL
  "0680512B CBB42C07 D47349D2 153B70C4 E5D7FDFC BFA36EA1 A85841B9 E46E09A2". 
Definition yG := bLtoN yGbL.
Definition nbL := hStobL
  "8542D69E 4C044F18 E8B92435 BF6FF7DD 29772063 0485628D 5AE74EE7 C32E79B7". 
Definition n := bLtoN nbL.
Definition M := strtobL "message digest". 
Definition dAbL := hStobL
  "128B2FA8 BD433C6C 068C8D80 3DFF7979 2A519A55 171B1B65 0C23661D 15897263". 
Definition dA := bLtoN dAbL.
Definition xAbL := hStobL
  "0AE4C779 8AA0F119 471BEE11 825BE462 02BB79E2 A5844495 E97C04FF 4DF2548A". 
Definition xA := bLtoN xAbL.
Definition yAbL := hStobL
  "7C0240F8 8F1CD4E1 6352A73C 17B7F16F 07353E53 A176D684 A9FE0C6B B798E857". 
Definition yA := bLtoN yAbL.
Definition ZA := hStobL 
  "F4A38489 E32B45B6 F876E3AC 2168CA39 2362DC8F 23459C1D 1146FC3D BFB7BC9A".
(*Example ZAtest : ComputeZ Hash ENTLa IDa abL bbL xGbL yGbL xAbL yAbL = ZA.
Proof. vm_compute. reflexivity. Qed. *)

Definition M_bart := ZA ++ M. 

(*
Compute bLtohS M_bart. 
*)

Definition ebL : bL := Hash M_bart.

(*
Compute bLtohS et. 
*)

Definition k := hStoN "6CB28D99 385C175C 94F94E93 4817663F C176D925 DD72B727 260DBAAE 1FB2F96F".

Definition x1 := hStoN "110FCDA5 7615705D 5E7B9324 AC4B856D 23E6D918 8B2AE477 59514657 CE25D112". 

Definition y1 := hStoN "1C65D68A 4A08601D F24B431E 0CAB4EBE 084772B3 817E8581 1A8510B2 DF7ECA1A". 

Definition field := pf_builder p Logic.eq_refl <: ECField .

Definition G := GE_wp field (xG, yG). 
Definition fa := wrapper field a.
Definition kG := pf_mul fa G k.
Definition P1 := GE_wp field (x1, y1).

Check GE_eqb kG P1. 

(*
Time Example kGeqP1 : GE_eqb kG P1 = true.
Proof. Time vm_compute. reflexivity. Qed. (*36s*)    
*)
(*
Definition rt := ((bLtoN et) + (bLtoN x1t)) mod (bLtoN nIn). 
(*
Compute NtohS rt. (* Correct *) 
*)

Definition factor1 := P_inv (bLtoN nIn)(1 + (bLtoN dAIn)) .
(*
Compute NtohS factor1. (*Correct, should be inverse on field n*)
*)
Definition factor2 := P_sub (bLtoN nIn)(bLtoN kt) (P_mul (bLtoN nIn) rt (bLtoN dAIn) ) . 
Definition nN := bLtoN nIn. 
Definition st := P_mul nN factor1 factor2.
(*
Compute NtohS st.
*)
(*Correct, 6FC6DAC3 2C5D5CF1 0C77DFB2 0F7C2EB6 67A45787 2FB09EC5 6327A67E C7DEEBE7 *)
*)
Definition  fb := wrapper field b.

Definition crv := pf_curve fa fb Logic.eq_refl. 

Time Compute match SigWithList Hash crv nbL xGbL yGbL ENTLa IDa
  dAbL xAbL yAbL M [k] with
| None => None
| Some (M, (r, s)) => Some (bLtostr M, ((bLtohS r), (bLtohS s)))
end. 
(*
= Some
("message digest",
("112438822fe71927b54e85bc2936c319343cbb7386cd0bd0e215184098032cf7",
"64912a6ef5b15fa686182a8490a9d3c0e9a1e6bdfa49de6522901f0bad65bea6"))
: option (string * (string * string))
Finished transaction in 40.152 secs (40.105u,0.035s) (successful)
Wrong. 
*)
(* Correct Finished transaction in 615.163 secs AC*)
(*  33.448 secs pf_mul_ps + pf_add_ac*)
(*Some
         ("message digest",
         ("40f1ec59f793d9f49e09dcef49130d4194f79fb1eed2caa55bacdb49c4e755d1",
         "6fc6dac32c5d5cf10c77dfb20f7c2eb667a457872fb09ec56327a67ec7deebe7"))
     : option (string * (string * string))
     *)

Definition tt := P_add nN rt st .

Definition x0't := hStoN "7DEACE5F D121BC38 5A3C6317 249F413D 28C17291 A60DFD83 B835A453 92D22B0A". 

Definition y0't := hStoN "2E49D5E5 279E5FA9 1E71FD8F 693A64A3 C4A94611 15A4FC9D 79F34EDC 8BDDEBD0". 

(*
Time Compute pf_mul  (bLtoN pIn) (bLtoN aIn) GIn st.  
Cop
         (56953972629032959544647951044806105100227418879105314443365623701807475862282,
         20936847120531059614594560449863630384405530616210027663248420985042997472208)
     : FEp
Finished transaction in 641.294 secs (640.154u,0.485s) (successful)
Correct! 
*)
Definition x00't := hStoN "1657FA75 BF2ADCDC 3C1F6CF0 5AB7B45E 04D3ACBE 8E4085CF A669CB25 64F17A9F". 

Definition y00't := hStoN "19F0115F 21E16D2F 5C3A485F 8575A128 BBCDDF80 296A62F6 AC2EB842 DD058E50". 

Definition P_At := Cop (bLtoN xAIn, bLtoN yAIn). 
(*
Time Compute pf_mul P_At tt (bLtoN pIn) (bLtoN aIn) . 
   = Cop
         (10106326974500318093811212845647691935066743080403682598448107247190051748511,
         11731984404579341477271988893658593900522406460222700443798045098506979741264)
     : FEp
Finished transaction in 623.69 secs (621.976u,0.888s) (successful)
Correct! 
*)
Definition x1't := hStoN "110FCDA5 7615705D 5E7B9324 AC4B856D 23E6D918 8B2AE477 59514657 CE25D112". 
Definition y1't := hStoN
  "1C65D68A 4A08601D F24B431E 0CAB4EBE 084772B3 817E8581 1A8510B2 DF7ECA1A". 
Definition P1t := pf_add (bLtoN pIn) (bLtoN aIn) (Cop (x0't, y0't)) (Cop (x00't, y00't)) .
(*Compute P1t. Correct*)
(*
Compute NtohS (P_add nN (bLtoN et) x1't).  (*Correct*)
*)
(*
Time Compute VeriSig_pf HashN (bLtoN pIn) (bLtoN aIn) nN (bLtoN xGIn)
  (bLtoN yGIn) (bLtoN xAIn) (bLtoN yAIn) (NtobL rt) (NtobL st) ZAt MIn. 
*)
(*
= None
     : option string
Finished transaction in 1247.005 secs (1245.699u,0.693s) (successful)
Correct! 
*)
End A_1. 
*)


Module A_2. 
Definition m := 257%N. 
Definition gp := (N.shiftl 1 257) + (N.shiftl 1 12) + 1. 
Definition b := false :: (hStobL "E78BCD09 746C2023 78A7E72B 12BCE002 66B9627E CB0B5A25 367AD1AD 4CC6242B"). 
Definition xG := false :: (hStobL "CDB9CA7F 1E6B0441 F658343F 4B10297C 0EF9B649 1082400A 62E7A748 5735FADD"). 
Definition yG := true :: (hStobL "3DE74DA6 5951C4D7 6DC89220 D5F7777A 611B1C38 BAE260B1 75951DC8 060C2B3E"). 
Definition n := hStobL "7FFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF BC972CF7 E6B6F900 945B3C6A 0CF6161D".
Definition M := strtobL "message digest".
Definition dA := hStobL "771EF3DB FF5F1CDC 32B9C572 93047619 1998B2BF 7CB981D7 F5B39202 645F0931".
Definition xA := true :: (hStobL "65961645 281A8626 607B917F 657D7E93 82F1EA5C D931F40F 6627F357 542653B2"). 
Definition yA := true :: (hStobL "68652213 0D590FB8 DE635D8F CA715CC6 BF3D05BE F3F75DA5 D5434544 48166612").
Definition k := hStobL "36CD79FC 8E24B735 7A8A7B4A 46D454C3 97703D64 98158C60 5399B341 ADA186D6". 
Definition IDa := hStobL "414C 49434531 32334059 41484F4F 2E434F4D".
Definition ENTLa := hStobL "0090". 

Definition e := hStoN "AD673CBD A3114171 29A9EAA5 F9AB1AA1 633AD477 18A84DFD 46C17C6F A0AA3B12". 
Definition x1 := hStoN "00 3FD87D69 47A15F94 25B32EDD 39381ADF D5E71CD4 BB357E3C 6A6E0397 EEA7CD66". 
Definition y1 := hStoN "00 80771114 6D73951E 9EB373A6 58214054 B7B56D1D 50B4CD6E B32ED387 A65AA6A2". 
 
Definition nN := bLtoN n. 
Definition r := hStobL "6D3FBA26 EAB2A105 4F5D1983 32E33581 7C8AC453 ED26D339 1CD4439D 825BF25B".
Definition s := hStobL "3124C568 8D95F0A1 0252A9BE D033BEC8 4439DA38 4621B6D6 FAD77F94 B74A9556". 
Definition G := Cop (bLtoN xG, bLtoN yG).
Definition a := NtobL_len 257 0. 

Definition Z_A := hStobL "26352AF8 2EC19F20 7BBC6F94 74E11E90 CE0F7DDA CE03B27F 801817E8 97A81FD5". 

(*
Time Compute bfp_mul m gp 0 G (bLtoN k). 
  *)
(*
* Cop
         (28878213983369220209949422064733326048509454351103134932255078508052236193126,
         58106417299780141903471788656951832429470650752450945419547271270608922125986)
     : GE
Finished transaction in 1146.773 secs (1143.449u,1.716s) (successful) 
*)
(*
Compute NtohS (P_add nN e x1). 
*)
(*
Time Compute match SigWithZAList_bfp HashN m gp a b n xG yG Z_A dA xA yA M [bLtoN k] with
  | None => None
  | Some (m',  (r, s)) => 
    Some (bLtostr m', ((bLtohS r), (bLtohS s)))
  end. 
*)
(*Correct*)
(*
Time Compute VeriSig_bfp HashN m gp (bLtoN a) (bLtoN n) (bLtoN xG) (bLtoN yG) (bLtoN xA) (bLtoN yA) r s Z_A M.
= None
     : option string
     *)
 (*
Finished transaction in 2264.387 secs (2254.81u,4.95s) (successful)
*)
End A_2. 
