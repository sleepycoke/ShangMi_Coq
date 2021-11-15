Require Import ECDef.

(*
Definition fd23 := pf_builder 23 Logic.eq_refl. 
Example pc010isInfO : PC_to_AC (GE_PC_wp fd23 (0, 1, 0)) = InfO fd23.
Proof. reflexivity. Qed. 
Compute PC_to_AC (GE_PC_wp fd23 (0, 1, 0)).
Compute GE_uwp (PC_to_AC (GE_PC_wp fd23 (7, 7, 7))).
Compute GE_uwp (PC_to_AC (GE_PC_wp fd23 (5, 5, 7))).
Compute GE_PC_eqb (AC_to_PC (PC_to_AC (GE_PC_wp fd23 (5, 5, 7))))
(GE_PC_wp fd23 (5, 5, 7)). 
 
Definition fd7 := pf_builder 7 Logic.eq_refl. 
Example pc112eqpc441 : GE_PC_eqb (GE_PC_wp fd7 (1, 1, 2))
 (GE_PC_wp fd7 (4, 4, 1)) = true := Logic.eq_refl. 

Example  pc112invpc431 : GE_PC_invb_pf (GE_PC_wp fd7 (1, 1, 2))
 (GE_PC_wp fd7 (4, 3, 1)) = true := Logic.eq_refl. 

(* Example 3 Page 12 *)
Definition fd19 : ECField := pf_builder 19 Logic.eq_refl . 
Example acdb102eq1516 : GE_uwp (pf_double_ac (wrapper fd19 1)
 (GE_wp fd19 (10, 2))) = (15, 16) := Logic.eq_refl.
Example ac102plus96eq163 : GE_uwp (pf_add_ac (wrapper fd19 1)
 (GE_wp fd19 (10, 2)) (GE_wp fd19 (9, 6))) = (16, 3) := Logic.eq_refl. 
Example pc102ml2eq1516 : GE_uwp (pf_mul_pc (wrapper fd19 1)
 (GE_wp fd19 (10, 2)) 2) = (15, 16) := Logic.eq_refl.
Example pc1021dbleq10177 : GE_PC_uwp (pf_double_pc (wrapper fd19 1)
 (GE_PC_wp fd19 (10, 2, 1))) = (10, 17, 7) := Logic.eq_refl . 

(* Example 6 *)
(*
Definition alpha := 2%N. 
Compute Bp_power 5 37 alpha 14. (* 29 correct *)
Compute Bp_power 5 37 alpha 31. (* 1 correct *)
Definition a6 := Bp_power 5 37 alpha 6. 
Definition a21 := Bp_power 5 37 alpha 21. 
Definition a3 := Bp_power 5 37 alpha 3. 
Definition a15 := Bp_power 5 37 alpha 15. 
Definition a24 := Bp_power 5 37 alpha 24. 
Definition a22 := Bp_power 5 37 alpha 22. 
Definition P1 := Cop (a6, a21). 
Definition P2 := Cop (a3, a15). 
Definition P3 := Cop (a24, a22). 

Compute bfp_double 5 37 1 P1 . (* 8, 31 correct *) 
Compute bfp_mul 5 37 1 P1 2 . (* 8, 31 correct *) 
Compute bfp_add 5 37 1 P1 P2 .  (* 30, 21 correct *)
*)
*)
Section pfmultest. 
Definition p := hStoN
  "8542D69E 4C044F18 E8B92435 BF6FF7DE 45728391 5C45517D 722EDB8B 08F1DFC3". 
Definition field := pf_builder p Logic.eq_refl.
Definition a := hStoN
  "787968B4 FA32C3FD 2417842E 73BBFEFF 2F3C848B 6831D7E0 EC65228B 3937E498". 
Definition fa := wrapper field a. 
Compute size p. 
(*
Definition x1 := hStoN
 "110FCDA5 7615705D 5E7B9324 AC4B856D 23E6D918 8B2AE477 59514657 CE25D112" .
Definition y1 := hStoN
 "1C65D68A 4A08601D F24B431E 0CAB4EBE 084772B3 817E8581 1A8510B2 DF7ECA1A" .
Definition P1 := GE_wp field (x1, y1). 
Definition x2 := hStoN "64D20D27 D0632957 F8028C1E 024F6B02 EDF23102 A566C932 AE8BD613 A8E865FE".
Definition y2 := hStoN "64D20D27 D0632957 F8028C1E 024F6B02 EDF23102 A566C932 AE8BD613 A8E865FE".
Definition P2 := GE_wp field (x2, y2). 
*)
(*
Time Compute GE_uwp (pf_mul_ac field (wrapper field a) P2 10). 
(*14.397 s.  46s if not using GE_uwp, amazing! *)
Time Compute GE_uwp (pf_mul_ac field (wrapper field a) P2 100). (*13.397 s*)
Time Compute GE_uwp (pf_mul_pc field (wrapper field a) P2 10). 
(* 3.371s using N, more than 3 mins by field, 3.822s using uwp! *)
Time Compute GE_uwp (pf_mul_pc field (wrapper field a) P2 100).
 (*13.397 s by N, 4.107s using uwp! *)
*)
(*
Time Compute pf_mul_ac p a P2 100. (*12.66 s*)
Time Compute pf_mul_ps p a P2 100. (*3.593 s*)

Time Compute pf_mul_ac p a P2 a. (*26.911 s*)
Time Compute pf_mul_ps p a P2 a. (*617.794 s*)
*)

Definition xG := hStoN
  "421DEBD6 1B62EAB6 746434EB C3CC315E 32220B3B ADD50BDC 4C4E6C14 7FEDD43D". 
Definition yG := hStoN
  "0680512B CBB42C07 D47349D2 153B70C4 E5D7FDFC BFA36EA1 A85841B9 E46E09A2". 

Definition k := hStoN 
  "6CB28D99 385C175C 94F94E93 4817663F C176D925 DD72B727 260DBAAE 1FB2F96F".
Definition G := GE_wp field (xG, yG). 
Definition kGac := pf_mul_ac fa G k.
(*Example kGaceqP1 : GE_eqb kGac P1 = true. 
Proof. Time vm_compute. reflexivity. Qed. 
(*705.683 secs vm_compute *)
*)
Definition kGpc := pf_mul_pc fa G k.  
(*
Example kGpceqP1 : GE_eqb kGpc P1 = true. 
Proof. Time vm_compute. reflexivity. Qed. 
(*35s*)
*)
Definition xA := hStoN "0AE4C779 8AA0F119 471BEE11 825BE462 02BB79E2 A5844495 E97C04FF 4DF2548A".
Definition yA := hStoN "7C0240F8 8F1CD4E1 6352A73C 17B7F16F 07353E53 A176D684 A9FE0C6B B798E857".
Definition PA := GE_wp field (xA, yA).
Definition t := hStoN "2B75F07E D7ECE7CC C1C8986B 991F441A D324D6D6 19FE06DD 63ED32E0 C997C801".
Definition x00 := hStoN "1657FA75 BF2ADCDC 3C1F6CF0 5AB7B45E 04D3ACBE 8E4085CF A669CB25 64F17A9F".
Definition y00 := hStoN "19F0115F 21E16D2F 5C3A485F 8575A128 BBCDDF80 296A62F6 AC2EB842 DD058E50".
Definition P00 := GE_wp field (x00, y00).
Example p00aceqPAt : GE_eqb P00 (pf_mul_ac fa PA t) = true .
Proof. Time vm_compute.  Qed.  (* 679.806 secs *)
End pfmultest.  