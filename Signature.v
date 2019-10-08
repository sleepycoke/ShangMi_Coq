Require Export SM2_SysPara.

(*5.5 trunk from right *)
(*TODO I really cannot understand its definition *)
Definition ENTL (ID : bL) :=
  N2bL_len 16 (N.of_nat (List.length (ID))). 

Open Scope list. 

Definition ComputeZ (ENTL_A ID_A a b xG yG xA yA : bL) :=
  Hash (ENTL_A ++ ID_A ++ a ++ b ++ xG ++ yG ++ xA ++ yA).

Definition TrySigWithk (k e n dA xG yG p a : N) : option (N * N) :=
  match pf_mul (Cop (xG, yG)) k p a with
  | InfO => None
  | Cop (x1, y1) => 
      let r := F_add e x1 n in
        if orb (N.eqb r 0) (N.eqb (r + k) n) then None else
        let s := F_mul (F_inv (F_add 1 dA n) n) (F_sub k (F_mul r dA n) n) n in
          if N.eqb s 0 then None else
          Some (r, s)
  end. 

Fixpoint TrySigWithList (klist : list N)(e n dA xG yG p a : N) : option (N * N) :=
  match klist with
  | [] => None
  | h :: tl =>
      match TrySigWithk h e n dA xG yG p a with
      | None => TrySigWithList tl e n dA xG yG p a
      | Some (r, s) => Some (r, s)
      end 
  end. 

(* 6.1 *)
(* TODO How to generate klist? *)
Definition SigWithList (klist : list N)(n dA xG yG p a Z_A M : bL) 
   : option (bL * (bL * bL)) :=
   let e := HashN (Z_A ++ M) in
     match TrySigWithList klist e (bL2N n) (bL2N dA) (bL2N xG) (bL2N yG)
        (bL2N p) (bL2N a) with
        | None => None
        | Some (r, s) => Some (M, ((N2bL r), (N2bL s)))
     end. 

(* true if x \in [lower, upper] *)
Definition inRange (x lower upper : N) : bool :=
  andb (leb lower x) (leb x upper). 

(* None if passed, otherwise Some error message *)
Definition VeriSig (n p a xG yG xA yA : N)(r'bL s'bL Z_A M' : bL) : option string :=
  let (r', s') := ((bL2N r'bL), (bL2N s'bL)) in
  if negb (inRange r' 1 (n - 1)) then Some "r' out of range" else
  if negb (inRange s' 1 (n - 1)) then Some "s' out of range" else
  let e' := HashN (Z_A ++ M') in
  let t := F_add r' s' n in
  if t =? 0 then Some "t = 0" else 
  let G := Cop (xG, yG) in
  let PA := Cop (xA, yA) in
  match pf_add (pf_mul G s' p a) (pf_mul PA t p a) p a with
  | InfO => Some "s'G + tPA = InfO"
  | Cop (x1', y1') => 
      let R := F_add e' x1' n in
      if R =? r' then None else Some "R != r'"
  end. 

  

(*
Module A_1. 
Definition IDa := hS2bL "414C 49434531 32334059 41484F4F 2E434F4D".
Definition ENTLa := hS2bL "0090". 
Compute IDa. 
Compute bL2hS (ENTL IDa).  (*TODO wrong, supposed to be 0090*)

Compute bL2bS ENTLa. 

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

Definition ZAt := Z_A ENTLa IDa aIn bIn xGIn yGIn xAIn yAIn. 
(*F4A38489 E32B45B6 F876E3AC 2168CA39 2362DC8F 23459C1D 1146FC3D BFB7BC9A*)
Compute bL2hS ZAt. (* Correct *)

Definition M_bart := ZAt ++ MIn. 

Compute bL2hS M_bart. 

Definition et := Hash M_bart.

Compute bL2hS et. 

Definition kt := hS2bL "6CB28D99 385C175C 94F94E93 4817663F C176D925 DD72B727 260DBAAE 1FB2F96F".

Definition x1t := hS2bL "110FCDA5 7615705D 5E7B9324 AC4B856D 23E6D918 8B2AE477 59514657 CE25D112". 

Definition y1t := hS2bL "1C65D68A 4A08601D F24B431E 0CAB4EBE 084772B3 817E8581 1A8510B2 DF7ECA1A". 

Definition GIn := Cop ((bL2N xGIn), (bL2N yGIn)). 
Definition kG := pf_mul GIn (bL2N kt) (bL2N pIn) (bL2N aIn).  

(* Time Compute kG. TODO is that possible to make it faster?  
  Cop
         (7717240450715166391686062596461402834004556820190931887479426615912677363986,
         12844692015861483985796897070387313459524129685989174230708833771946472557082)
     : FEp
Finished transaction in 618.101 secs (617.552u,0.299s) (successful)
Correct! 
*)
Definition rt := ((bL2N et) + (bL2N x1t)) mod (bL2N nIn). 
Compute N2hS rt. (* Correct *) 

Definition factor1 := inv_p (1 + (bL2N dAIn)) (bL2N nIn).
Compute N2hS factor1. (*Correct, should be inverse on field n*)

Definition factor2 := F_sub (bL2N kt) (F_mul rt (bL2N dAIn) (bL2N nIn)) (bL2N nIn). 
Definition nN := bL2N nIn. 
Definition st := F_mul factor1 factor2 nN.

Compute N2hS st. (*Correct*) 
(* Correct Finished transaction in 615.163 secs 
Time Compute SigWithList [bL2N kt] nIn dAIn xGIn yGIn pIn aIn ZAt MIn.  
  *)

Definition tt := F_add rt st nN.

Definition x0't := hS2N "7DEACE5F D121BC38 5A3C6317 249F413D 28C17291 A60DFD83 B835A453 92D22B0A". 

Definition y0't := hS2N "2E49D5E5 279E5FA9 1E71FD8F 693A64A3 C4A94611 15A4FC9D 79F34EDC 8BDDEBD0". 

(*
Time Compute pf_mul GIn st (bL2N pIn) (bL2N aIn).  
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
Time Compute pf_mul P_At tt (bL2N pIn) (bL2N aIn). 
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
Print pf_add. 
Definition P1t := pf_add (Cop (x0't, y0't)) (Cop (x00't, y00't)) (bL2N pIn) (bL2N aIn).
(*Compute P1t. Correct*)
Compute N2hS (F_add (bL2N et) x1't nN).  (*Correct*)

(*
Time Compute VeriSig nN (bL2N pIn) (bL2N aIn) (bL2N xGIn)
  (bL2N yGIn) (bL2N xAIn) (bL2N yAIn) (N2bL rt) (N2bL st) ZAt MIn. 
= None
     : option string
Finished transaction in 1247.005 secs (1245.699u,0.693s) (successful)
Correct! 
*)
End A_1. 
*)
