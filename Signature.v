Require Export SM2_SysPara.

(*5.5 trunk from right *)
(*TODO I really cannot understand its definition *)
Definition ENTL (ID : bL) :=
  N2bL_len (N.of_nat (List.length (ID))) 16. 

Open Scope list. 

Definition Z_A (ENTL_A ID_A a b xG yG xA yA : bL) :=
  Hash (ENTL_A ++ ID_A ++ a ++ b ++ xG ++ yG ++ xA ++ yA).

Print pf_mul.
Print FEp. 

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

Module A_1. 
Definition IDa := hS2bL "414C 49434531 32334059 41484F4F 2E434F4D".
Definition ENTLa := hS2bL "0090". 
Compute IDa. 
Compute bL2hS (ENTL IDa).  (*TODO wrong, supposed to be 0090*)

Compute bL2bS ENTLa. 

Module A_2_1. 
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

Definition Pin := Cop ((bL2N xGIn), (bL2N yGIn)). 
Definition kG := pf_mul Pin (bL2N kt) (bL2N pIn) (bL2N aIn).  

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

End A_2_1. 
End A_1. 

