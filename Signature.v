(*Require Export SysPara.*)
Require Export ECAlg.
Require Export SM3. 

(*5.5 trunk from right *)
(*TODO I really cannot understand its definition *)
Definition ENTL (ID : bL) :=
  N2bL_len 16 (N.of_nat (List.length (ID))). 

Open Scope list. 

Definition ComputeZ (ENTL_A ID_A a b xG yG xA yA : bL) :=
  Hash (ENTL_A ++ ID_A ++ a ++ b ++ xG ++ yG ++ xA ++ yA).

Definition TrySigWithk (ml : GE -> N -> GE)(n xG yG dA e k : N) : option (N * N) :=
  match ml (Cop (xG, yG)) k with
  | InfO => None
  | Cop (x1, y1) => 
      let r := P_add n e x1 in
        if orb (N.eqb r 0) (N.eqb (r + k) n) then None else
        let s := P_mul n (P_inv n (P_add n 1 dA)) (P_sub n k (P_mul n r dA)) in
          if N.eqb s 0 then None else
          Some (r, s)
  end. 

Fixpoint TrySigWithList (ml : GE -> N -> GE)(n xG yG dA e : N)(klist : list N) : option (N * N) :=
  match klist with
  | [] => None
  | h :: tl =>
      match TrySigWithk ml n xG yG dA e h with
      | None => TrySigWithList ml n xG yG dA e tl
      | Some (r, s) => Some (r, s)
      end 
  end. 

(* 6.1 *)
(* TODO How to generate klist? *)
Definition SigWithZAList (ml : GE -> N -> GE)(a b n xG yG Z_A dA xA yA M : bL)(klist : list N)
   : option (bL * (bL * bL)) :=
   let e := HashN (Z_A ++ M) in
     match TrySigWithList ml (bL2N n)
     (bL2N xG) (bL2N yG) (bL2N dA) e klist with
        | None => None
        | Some (r, s) => Some (M, ((N2bL r), (N2bL s)))
     end. 

Definition SigWithList (ml : GE -> N -> GE)(a b n xG yG ENTL_A ID_A dA xA yA M : bL)(klist : list N)
   : option (bL * (bL * bL)) :=
   let Z_A := ComputeZ ENTL_A ID_A a b xG yG xA yA in
   SigWithZAList ml a b n xG yG Z_A dA xA yA M klist. 

Definition SigWithList_pf (p a b n xG yG ENTL_A ID_A dA xA yA M : bL)(klist : list N)
   : option (bL * (bL * bL)) :=
   SigWithList (pf_mul (bL2N p) (bL2N a)) a b n xG yG ENTL_A ID_A dA xA yA M klist. 

Definition SigWithList_bfp (m gp : N)(a b n xG yG ENTL_A ID_A dA xA yA M : bL)(klist : list N)
   : option (bL * (bL * bL)) :=
   SigWithList (bfp_mul m gp (bL2N a)) a b n xG yG ENTL_A ID_A dA xA yA M klist. 

Definition SigWithZAList_bfp (m gp : N)(a b n xG yG ZA dA xA yA M : bL)(klist : list N)
   : option (bL * (bL * bL)) :=
   SigWithZAList (bfp_mul m gp (bL2N a)) a b n xG yG ZA dA xA yA M klist. 

(* true if x \in [lower, upper] *)
Definition inRange (x lower upper : N) : bool :=
  andb (leb lower x) (leb x upper). 

(* None if passed, otherwise Some error message *)
Definition VeriSig (ml : GE -> N -> GE)(ad : GE -> GE -> GE)(n xG yG xA yA : N)(r'bL s'bL Z_A M' : bL) : option string :=
  let (r', s') := ((bL2N r'bL), (bL2N s'bL)) in
  if negb (inRange r' 1 (n - 1)) then Some "r' out of range" else
  if negb (inRange s' 1 (n - 1)) then Some "s' out of range" else
  let e' := HashN (Z_A ++ M') in
  let t := P_add n r' s' in
  if t =? 0 then Some "t = 0" else 
  let G := Cop (xG, yG) in
  let PA := Cop (xA, yA) in
  match ad (ml G s') (ml PA t) with
  | InfO => Some "s'G + tPA = InfO"
  | Cop (x1', y1') => 
      let R := P_add n e' x1' in
      if R =? r' then None else Some "R != r'"
  end. 

  
Definition VeriSig_pf (p a n xG yG xA yA : N)(r'bL s'bL Z_A M' : bL) : option string :=
  VeriSig (pf_mul p a) (pf_add p a) n xG yG xA yA r'bL s'bL Z_A M'. 

Definition VeriSig_bfp (m gp a n xG yG xA yA : N)(r'bL s'bL Z_A M' : bL) : option string :=
  VeriSig (bfp_mul m gp a) (bfp_add m gp a) n xG yG xA yA r'bL s'bL Z_A M'. 

(*
Module A_1. 
Definition IDa := hS2bL "414C 49434531 32334059 41484F4F 2E434F4D".
Definition ENTLa := hS2bL "0090". 
(*
Compute IDa. 
Compute bL2hS (ENTL IDa).  

Compute bL2bS ENTLa. 
*)

Definition pIn := hS2bL 
  "8542D69E 4C044F18 E8B92435 BF6FF7DE 45728391 5C45517D 722EDB8B 08F1DFC3".
Definition aIn := hS2bL
  "787968B4 FA32C3FD 2417842E 73BBFEFF 2F3C848B 6831D7E0 EC65228B 3937E498". 
Definition bIn := hS2bL
  "63E4C6D3 B23B0C84 9CF84241 484BFE48 F61D59A5 B16BA06E 6E12D1DA 27C5249A". 
Definition xGIn := hS2bL
  "421DEBD6 1B62EAB6 746434EB C3CC315E 32220B3B ADD50BDC 4C4E6C14 7FEDD43D". 
Definition yGIn := hS2bL
  "0680512B CBB42C07 D47349D2 153B70C4 E5D7FDFC BFA36EA1 A85841B9 E46E09A2". 
Definition nIn := hS2bL
  "8542D69E 4C044F18 E8B92435 BF6FF7DD 29772063 0485628D 5AE74EE7 C32E79B7". 
Definition MIn := str2bL "message digest". 
Definition dAIn := hS2bL
  "128B2FA8 BD433C6C 068C8D80 3DFF7979 2A519A55 171B1B65 0C23661D 15897263". 
Definition xAIn := hS2bL
  "0AE4C779 8AA0F119 471BEE11 825BE462 02BB79E2 A5844495 E97C04FF 4DF2548A". 
Definition yAIn := hS2bL
  "7C0240F8 8F1CD4E1 6352A73C 17B7F16F 07353E53 A176D684 A9FE0C6B B798E857". 

Definition ZAt := ComputeZ ENTLa IDa aIn bIn xGIn yGIn xAIn yAIn. 
(*F4A38489 E32B45B6 F876E3AC 2168CA39 2362DC8F 23459C1D 1146FC3D BFB7BC9A*)
(*
Compute bL2hS ZAt. (* Correct *)
*)

Definition M_bart := ZAt ++ MIn. 

(*
Compute bL2hS M_bart. 
*)

Definition et := Hash M_bart.

(*
Compute bL2hS et. 
*)

Definition kt := hS2bL "6CB28D99 385C175C 94F94E93 4817663F C176D925 DD72B727 260DBAAE 1FB2F96F".

Definition x1t := hS2bL "110FCDA5 7615705D 5E7B9324 AC4B856D 23E6D918 8B2AE477 59514657 CE25D112". 

Definition y1t := hS2bL "1C65D68A 4A08601D F24B431E 0CAB4EBE 084772B3 817E8581 1A8510B2 DF7ECA1A". 

Definition GIn := Cop ((bL2N xGIn), (bL2N yGIn)). 
Definition kG := pf_mul (bL2N pIn) (bL2N aIn) GIn (bL2N kt).    

(*Time Compute kG. (*TODO is that possible to make it faster?  *)
  Cop
         (7717240450715166391686062596461402834004556820190931887479426615912677363986,
         12844692015861483985796897070387313459524129685989174230708833771946472557082)
     : FEp
Finished transaction in 618.101 secs (617.552u,0.299s) (successful)
Correct! 
*)
Definition rt := ((bL2N et) + (bL2N x1t)) mod (bL2N nIn). 
(*
Compute N2hS rt. (* Correct *) 
*)

Definition factor1 := P_inv (bL2N nIn)(1 + (bL2N dAIn)) .
(*
Compute N2hS factor1. (*Correct, should be inverse on field n*)
*)
Definition factor2 := P_sub (bL2N nIn)(bL2N kt) (P_mul (bL2N nIn) rt (bL2N dAIn) ) . 
Definition nN := bL2N nIn. 
Definition st := P_mul nN factor1 factor2.
(*
Compute N2hS st.
*)
(*Correct, 6FC6DAC3 2C5D5CF1 0C77DFB2 0F7C2EB6 67A45787 2FB09EC5 6327A67E C7DEEBE7 *)
(*
Time Compute match SigWithList_pf pIn aIn bIn nIn xGIn yGIn ENTLa IDa dAIn xAIn yAIn MIn [bL2N kt] with
| None => None
| Some (M, (r, s)) => Some (bL2str M, ((bL2hS r), (bL2hS s)))
end. 
*)
(* Correct Finished transaction in 615.163 secs *)
(*Some
         ("message digest",
         ("40f1ec59f793d9f49e09dcef49130d4194f79fb1eed2caa55bacdb49c4e755d1",
         "6fc6dac32c5d5cf10c77dfb20f7c2eb667a457872fb09ec56327a67ec7deebe7"))
     : option (string * (string * string))
     *)

Definition tt := P_add nN rt st .

Definition x0't := hS2N "7DEACE5F D121BC38 5A3C6317 249F413D 28C17291 A60DFD83 B835A453 92D22B0A". 

Definition y0't := hS2N "2E49D5E5 279E5FA9 1E71FD8F 693A64A3 C4A94611 15A4FC9D 79F34EDC 8BDDEBD0". 

(*
Time Compute pf_mul  (bL2N pIn) (bL2N aIn) GIn st.  
Cop
         (56953972629032959544647951044806105100227418879105314443365623701807475862282,
         20936847120531059614594560449863630384405530616210027663248420985042997472208)
     : FEp
Finished transaction in 641.294 secs (640.154u,0.485s) (successful)
Correct! 
*)
Definition x00't := hS2N "1657FA75 BF2ADCDC 3C1F6CF0 5AB7B45E 04D3ACBE 8E4085CF A669CB25 64F17A9F". 

Definition y00't := hS2N "19F0115F 21E16D2F 5C3A485F 8575A128 BBCDDF80 296A62F6 AC2EB842 DD058E50". 

Definition P_At := Cop (bL2N xAIn, bL2N yAIn). 
(*
Time Compute pf_mul P_At tt (bL2N pIn) (bL2N aIn) . 
   = Cop
         (10106326974500318093811212845647691935066743080403682598448107247190051748511,
         11731984404579341477271988893658593900522406460222700443798045098506979741264)
     : FEp
Finished transaction in 623.69 secs (621.976u,0.888s) (successful)
Correct! 
*)
Definition x1't := hS2N "110FCDA5 7615705D 5E7B9324 AC4B856D 23E6D918 8B2AE477 59514657 CE25D112". 
Definition y1't := hS2N
  "1C65D68A 4A08601D F24B431E 0CAB4EBE 084772B3 817E8581 1A8510B2 DF7ECA1A". 
Definition P1t := pf_add (bL2N pIn) (bL2N aIn) (Cop (x0't, y0't)) (Cop (x00't, y00't)) .
(*Compute P1t. Correct*)
(*
Compute N2hS (P_add nN (bL2N et) x1't).  (*Correct*)
*)
(*
Time Compute VeriSig_pf (bL2N pIn) (bL2N aIn) nN (bL2N xGIn)
  (bL2N yGIn) (bL2N xAIn) (bL2N yAIn) (N2bL rt) (N2bL st) ZAt MIn. 
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
Definition b := false :: (hS2bL "E78BCD09 746C2023 78A7E72B 12BCE002 66B9627E CB0B5A25 367AD1AD 4CC6242B"). 
Definition xG := false :: (hS2bL "CDB9CA7F 1E6B0441 F658343F 4B10297C 0EF9B649 1082400A 62E7A748 5735FADD"). 
Definition yG := true :: (hS2bL "3DE74DA6 5951C4D7 6DC89220 D5F7777A 611B1C38 BAE260B1 75951DC8 060C2B3E"). 
Definition n := hS2bL "7FFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF BC972CF7 E6B6F900 945B3C6A 0CF6161D".
Definition M := str2bL "message digest".
Definition dA := hS2bL "771EF3DB FF5F1CDC 32B9C572 93047619 1998B2BF 7CB981D7 F5B39202 645F0931".
Definition xA := true :: (hS2bL "65961645 281A8626 607B917F 657D7E93 82F1EA5C D931F40F 6627F357 542653B2"). 
Definition yA := true :: (hS2bL "68652213 0D590FB8 DE635D8F CA715CC6 BF3D05BE F3F75DA5 D5434544 48166612").
Definition k := hS2bL "36CD79FC 8E24B735 7A8A7B4A 46D454C3 97703D64 98158C60 5399B341 ADA186D6". 
Definition IDa := hS2bL "414C 49434531 32334059 41484F4F 2E434F4D".
Definition ENTLa := hS2bL "0090". 

Definition e := hS2N "AD673CBD A3114171 29A9EAA5 F9AB1AA1 633AD477 18A84DFD 46C17C6F A0AA3B12". 
Definition x1 := hS2N "00 3FD87D69 47A15F94 25B32EDD 39381ADF D5E71CD4 BB357E3C 6A6E0397 EEA7CD66". 
Definition y1 := hS2N "00 80771114 6D73951E 9EB373A6 58214054 B7B56D1D 50B4CD6E B32ED387 A65AA6A2". 
 
Definition nN := bL2N n. 
Definition r := hS2bL "6D3FBA26 EAB2A105 4F5D1983 32E33581 7C8AC453 ED26D339 1CD4439D 825BF25B".
Definition s := hS2bL "3124C568 8D95F0A1 0252A9BE D033BEC8 4439DA38 4621B6D6 FAD77F94 B74A9556". 
Definition G := Cop (bL2N xG, bL2N yG).
Definition a := N2bL_len 257 0. 

Definition Z_A := hS2bL "26352AF8 2EC19F20 7BBC6F94 74E11E90 CE0F7DDA CE03B27F 801817E8 97A81FD5". 

(* TODO how to ComputeZ ? *)
(*
Compute bL2hS (ComputeZ ENTLa IDa a b xG yG xA yA). 
Compute bL2hS (ComputeZ ENTLa IDa [] b xG yG xA yA). 
Compute bL2hS (ComputeZ ENTLa IDa [false] b xG yG xA yA). 
Compute bL2hS (ComputeZ ENTLa IDa [false; false] b xG yG xA yA). 
Compute bL2hS (ComputeZ ENTLa IDa [false; false; false] b xG yG xA yA). 
Compute bL2hS (ComputeZ ENTLa IDa [false; false; false; false] b xG yG xA yA). 
Compute bL2hS (ComputeZ ENTLa IDa [false; false; false; false; false] b xG yG xA yA). 
Compute bL2hS (ComputeZ ENTLa IDa [false; false; false; false; false; false] b xG yG xA yA). 
Compute bL2hS (ComputeZ ENTLa IDa [false; false; false; false; false; false; false] b xG yG xA yA). 
Compute bL2hS (ComputeZ ENTLa IDa [false; false; false; false; false; false; false; false] b xG yG xA yA). 
Compute bL2hS (ComputeZ ENTLa IDa [false; false; false; false; false; false; false; false; false] b xG yG xA yA). 
*)

(*
Time Compute bfp_mul m gp 0 G (bL2N k). 
  *)
(*
* Cop
         (28878213983369220209949422064733326048509454351103134932255078508052236193126,
         58106417299780141903471788656951832429470650752450945419547271270608922125986)
     : GE
Finished transaction in 1146.773 secs (1143.449u,1.716s) (successful) 
*)
(*
Compute N2hS (P_add nN e x1). 
*)
(*
Time Compute match SigWithZAList_bfp m gp a b n xG yG Z_A dA xA yA M [bL2N k] with
  | None => None
  | Some (m',  (r, s)) => 
    Some (bL2str m', ((bL2hS r), (bL2hS s)))
  end. 
*)
(*Correct*)
(*
Time Compute VeriSig_bfp m gp (bL2N a) (bL2N n) (bL2N xG) (bL2N yG) (bL2N xA) (bL2N yA) r s Z_A M.
= None
     : option string
     *)
 (*
Finished transaction in 2264.387 secs (2254.81u,4.95s) (successful)
*)
End A_2. 
