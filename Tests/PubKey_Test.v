Require Import PubKey.
Open Scope ecfield_scope. 
Module test_pf. 
Definition A2_E2_begin_description := "Example 2 of A.2 on SM2p4 Annex A, page 10, begins. ". 
Print A2_E2_begin_description. 
Definition p := hStoN 
  "8542D69E 4C044F18 E8B92435 BF6FF7DE 45728391 5C45517D 722EDB8B 08F1DFC3".
Definition field := pf_builder p Logic.eq_refl.
Definition aN := hStoN 
  "787968B4 FA32C3FD 2417842E 73BBFEFF 2F3C848B 6831D7E0 EC65228B 3937E498".
Definition a := wrapper field aN.
Definition bN := hStoN
  "63E4C6D3 B23B0C84 9CF84241 484BFE48 F61D59A5 B16BA06E 6E12D1DA 27C5249A".
Definition b := wrapper field bN.
Definition crv := @pf_curve _ field a b Logic.eq_refl.
Definition xGN := hStoN
  "421DEBD6 1B62EAB6 746434EB C3CC315E 32220B3B ADD50BDC 4C4E6C14 7FEDD43D".
Definition xG := wrapper field xGN.
Definition yGN := hStoN 
  "0680512B CBB42C07 D47349D2 153B70C4 E5D7FDFC BFA36EA1 A85841B9 E46E09A2". 
Definition yG := wrapper field yGN.
Definition n := hStoN 
  "8542D69E 4C044F18 E8B92435 BF6FF7DD 29772063 0485628D 5AE74EE7 C32E79B7".
Definition h := 1%N.  (* By Hasse Thm *)
Definition M := hStobL "656E63 72797074 696F6E20 7374616E 64617264".
Definition dB := hStoN 
  "1649AB77 A00637BD 5E2EFE28 3FBF3535 34AA7F7C B89463F2 08DDBC29 20BB0DA0".
Definition xBN := hStoN
  "435B39CC A8F3B508 C1488AFC 67BE491A 0F7BA07E 581A0E48 49A5CF70 628A7E0A".
Definition xB := wrapper field xBN.
Definition yBN := hStoN
  "75DDBA78 F15FEECB 4C7895E2 C1CDF5FE 01DEBB2C DBADF453 99CCF77B BA076A42".
Definition yB := wrapper field yBN.
Definition k := hStoN 
  "4C62EEFD 6ECFC2B9 5B92FD6C 3D957514 8AFA1742 5546D490 18E5388D 49DD7B4F".

Definition G := Cop field (xG, yG).
Definition PB := Cop field (xB, yB).
Definition klen := length M.  
  (* Obsolete
Time Check match TryComputeTwithK k p a h ucp G PB klen SM3_Hash constant_v with
  | Error s => Error s
  | Normal None => Normal None
  | Normal (Some (a, b, c, d)) =>
      Normal (Some (bLtohS a, bLtohS b, bLtohS c, bLtohS d))
end. 
*)

(*
  = Normal
         (Some
            ("006e30dae231b071dfad8aa379e90264491603",
            "64d20d27d0632957f8028c1e024f6b02edf23102a566c932ae8bd613a8e865fe",
            "58d225eca784ae300a81a2d48281a828e1cedf11c4219099840265375077bf78",
            "04245c26fb68b1ddddb12c4b6bf9f2b6d5fe60a383b0d18d1c4144abf17f6252e776cb9264c2a7e88e52b19903fdc47378f605e36811f5c07423a24b84400f01b8"))
     : optErr (option (string * string * string * string))
Finished transaction in 1243.719 secs (1241.274u,1.171s) (successful) 
Correct
*)
Definition C := hStobL "04245C26 FB68B1DD DDB12C4B 6BF9F2B6 D5FE60A3 83B0D18D
 1C4144AB F17F6252 E776CB92 64C2A7E8 8E52B199 03FDC473 78F605E3 6811F5C0 
 7423A24B 84400F01 B8650053 A89B41C4 18B0C3AA D00D886C 00286467 9C3D7360
  C30156FA B7C80A02 76712DA9 D8094A63 4B766D3A 285E0748 0653426D". 
Example cmpCtest_pf : Normal C = 
  ComputeCwithklist SM3_Hash constant_v klen crv h [k] ucp G PB M. 
Proof. Time vm_compute. (* 75s *) reflexivity. Qed.
(*
Time Compute match ComputeCwithklist_pf SM3_Hash constant_v p a h [k] ucp (Cop (xG, yG)) (Cop (xB, yB)) M with
| Error s => Error s
| Normal bl => Normal (bLtohS bl)
end. 
*)
(*
= Normal
         "04245c26fb68b1ddddb12c4b6bf9f2b6d5fe60a383b0d18d1c4144abf17f6252e776cb9264c2a7e88e52b19903fdc47378f605e36811f5c07423a24b84400f01b8650053a89b41c418b0c3aad00d886c002864679c3d7360c30156fab7c80a0276712da9d8094a634b766d3a285e07480653426d"
     : optErr string
Finished transaction in 1239.021 secs (1237.408u,0.874s) (successful)
Correct
*)
(*Example cmpM'test_pf : Normal M = 
  ComputeM' SM3_Hash constant_v klen ucp crv p h dB C. 
Proof. Time vm_compute. (*39s*) reflexivity. Qed. *)
(*
Time Compute match ComputeM'_pf SM3_Hash constant_v klen p a b h dB ucp C with
| Error s => Error s
| Normal bl => Normal (bLtohS bl)
end. 
*)
(*
* = Normal "656e6372797074696f6e207374616e64617264"
     : optErr string
Finished transaction in 612.356 secs (611.425u,0.411s) (successful)
Correct
*)
Definition A2_end_description := "Example 2 of A.2 on SM2p4 Annex A, page 10, ended. ". 
Print A2_end_description. 
End test_pf. 

(*Module test_bfp.
Definition m := 257%N.
Definition gp := (N.shiftl 1 257) + (N.shiftl 1 12) + 1. 
Definition a := 0%N.
Definition b := hStoN "00 E78BCD09 746C2023 78A7E72B 12BCE002 66B9627E CB0B5A25 367AD1AD 4CC6242B".
Definition h := 4%N. 
Definition xG := hStoN "00 CDB9CA7F 1E6B0441 F658343F 4B10297C 0EF9B649 1082400A 62E7A748 5735FADD".
Definition yG := hStoN "01 3DE74DA6 5951C4D7 6DC89220 D5F7777A 611B1C38 BAE260B1 75951DC8 060C2B3E".
Definition G := Cop (xG, yG). 
Definition n := hStoN "7FFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF BC972CF7 E6B6F900 945B3C6A 0CF6161D". 
Definition M := hStobL "656E63 72797074 696F6E20 7374616E 64617264".
Definition klen := 152%nat. 
Definition dB := hStoN "56A270D1 7377AA9A 367CFA82 E46FA526 7713A9B9 1101D077 7B07FCE0 18C757EB".
Definition xB := hStoN "00 A67941E6 DE8A6180 5F7BCFF0 985BB3BE D986F1C2 97E4D888 0D82B821 C624EE57". 
Definition yB := hStoN "01 93ED5A67 07B59087 81B86084 1085F52E EFA7FE32 9A5C8118 43533A87 4D027271". 
Definition PB := Cop (xB, yB). 
Definition k := hStoN "6D3B4971 53E3E925 24E5C122 682DBDC8 705062E2 0B917A5F 8FCDB8EE 4C66663D". 
Definition x1 := hStoN "01 9D236DDB 305009AD 52C51BB9 32709BD5 34D476FB B7B0DF95 42A8A4D8 90A3F2E1". 
Definition y1 := hStoN "00 B23B938D C0A94D1D F8F42CF4 5D2D6601 BF638C3D 7DE75A29 F02AFB7E 45E91771". 

Definition x2 := hStoN "00 83E628CF 701EE314 1E8873FE 55936ADF 24963F5D C9C64805 66C80F8A 1D8CC51B".
Definition y2 := hStoN "01 524C647F 0C0412DE FD468BDA 3AE0E5A8 0FCC8F5C 990FEE11 60292923 2DCD9F36". 
Definition P2 := Cop (x2, y2). 
Definition t := KDF ((NtoBbL_len 257 x2) ++ (NtoBbL_len 257 y2)) klen SM3_Hash constant_v. 
(*Compute bLtohS t.*) (*Correct*)
Definition C2 := bLXOR M t . 
(*Compute bLtohS C2.*) (*Correct*)
Definition C3 := SM3_Hash ((NtoBbL_len 257 x2) ++ M ++ (NtoBbL_len 257 y2)). 
(*Compute bLtohS C3. *)(*Correct*) 
(*
Time Compute match ComputeCwithklist_bfp SM3_Hash constant_v m gp a h [k] ucp G PB M with
| Error s => Error s
| Normal bl => Normal (bLtohS bl)
end. 
*)
(*
= Normal
         "04019d236ddb305009ad52c51bb932709bd534d476fbb7b0df9542a8a4d890a3f2e1b23b938dc0a94d1df8f42cf45d2d6601bf638c3d7de75a29f02afb7e45e91771fd55ac6213c2a8a040e4cab5b26a9cfcda737373a48625d3758fa37b3eab80e9cfcaba665e3199ea15a1fa8189d96f579125e4"
     : optErr string
Finished transaction in 2365.322 secs (2340.379u,5.914s) (successful)
x1 C2 C3 are correcet, C2 missing leading 00
*)
Definition C1C2C3 := hStobL "04019d236ddb305009ad52c51bb932709bd534d476fbb7b0df9542a8a4d890a3f2e100b23b938dc0a94d1df8f42cf45d2d6601bf638c3d7de75a29f02afb7e45e91771fd55ac6213c2a8a040e4cab5b26a9cfcda737373a48625d3758fa37b3eab80e9cfcaba665e3199ea15a1fa8189d96f579125e4". 

Definition C := hStobL "04019D23 6DDB3050 09AD52C5 1BB93270 9BD534D4 76FBB7B0 DF9542A8 A4D890A3 F2E100B2 3B938DC0 A94D1DF8 F42CF45D 2D6601BF 638C3D7D E75A29F0 2AFB7E45 E91771FD 55AC6213 C2A8A040 E4CAB5B2 6A9CFCDA 737373A4 8625D375 8FA37B3E AB80E9CF CABA665E 3199EA15 A1FA8189 D96F5791 25E4". 
(*
Compute bLXOR C1C2C3 C. 
Compute List.length C1C2C3.
Compute List.length C. 
Correct *)
(*
Time Compute match ComputeM'_bfp SM3_Hash constant_v klen m gp a b h dB ucp C with
| Error s => Error s
| Normal bl => Normal (bLtohS bl)
end. 
*)
(*
= Normal "656e6372797074696f6e207374616e64617264"
     : optErr string
*)
(*
Definition M' := hStobL "656e6372797074696f6e207374616e64617264".
Compute bLXOR M  M'. 
*)
(*Correct *)
End test_bfp.
*)
