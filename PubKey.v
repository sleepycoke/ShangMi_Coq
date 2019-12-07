Require Export KeyEx.

(*A2 - A5 *)


(* A1 - A8 *)
Definition TryComputeTwithK (k p a h : N)(cp : cmp_type)(G PB : GE)
 (klen : nat)(hash_v : bL -> bL)(v : nat) : optErr (option (bL * bL * bL * bL)) :=
  let C1 := pf_mul G k p a in
  match C1 with
  | InfO => Error "C1 = InfO" (* impossible since k < n *)
  | Cop (x1, y1) =>
    let C1bl := BL2bL (Point2BL_p x1 y1 cp) in
    let S := pf_mul PB h p a in
    match S with
    | InfO => Error "S = InfO"
    | _ =>
        let kPB := pf_mul PB k p a in
        match kPB with
        | InfO => Error "kPB = InfO" (* impossible? *)
        | Cop (x2, y2) => 
          let (x2bl, y2bl) := (N2BbL x2, N2BbL y2) in
          let t := KDF (x2bl ++ y2bl) klen hash_v v in
           if All0bL t then Normal None
           else Normal (Some (t, x2bl, y2bl, C1bl))
        end
    end
  end. 

Fixpoint ComputeCwithklist (M : bL)(klist : list N)(p a h : N)(cp : cmp_type)
  (G PB : GE)(hash_v : bL -> bL)(v : nat) : optErr bL :=
  match klist with
  | [] => Error "klist depleted"
  | k :: tl =>
      match TryComputeTwithK k p a h cp G PB (length M) hash_v v with
      | Error err => Error (err ++ " k = " ++ (N2hS k))
      | Normal None =>
          ComputeCwithklist M tl p a h cp G PB hash_v v
      | Normal (Some (t, x2bl, y2bl, C1bl)) =>
          let C2 := bLXOR M t in
          let C3 := hash_v (x2bl ++ M ++ y2bl) in
            Normal (C1bl ++ C2 ++ C3)
      end
  end. 


(* B1 - B7 *)
Definition ComputeM' (C : bL)(p a b h dB : N)(cp : cmp_type)(klen : nat)(hash_v : bL -> bL)(v : nat) : optErr bL :=
  let (C1bl, C2C3) := partListBack C (Nat.add klen v) in
  match BL2Point_p p a b (bL2BL C1bl) cp with
  | None => Error "Failed to uncompress C1"
  | Some (x1, y1) =>
    if negb (OnCurve x1 y1 p a b) then Error "C1 not on curve"
    else let C1 := Cop (x1, y1) in
    let S := pf_mul C1 h p a in
    match S with
    | InfO => Error "S = InfO"
    | _ =>
        let dBC1 := pf_mul C1 dB p a in
        match dBC1 with
        | InfO => Error "dBC1 = InfO"
        | Cop (x2, y2) =>
            let (x2bl, y2bl) := (N2BbL x2, N2BbL y2) in
            let t := KDF (x2bl ++ y2bl) klen hash_v v in
            if All0bL t then Error "t is all 0s" else
            let (C2, C3) := partList C2C3 klen in
            let M' := bLXOR C2 t in
            let u := hash_v (x2bl ++ M' ++ y2bl) in
            if negb (bLeqb u C3) then Error "u != C3"
            else Normal M'
        end
    end
  end. 

          


Module test. 
Definition p := hS2N "8542D69E 4C044F18 E8B92435 BF6FF7DE 45728391 5C45517D 722EDB8B 08F1DFC3".
Definition a := hS2N "787968B4 FA32C3FD 2417842E 73BBFEFF 2F3C848B 6831D7E0 EC65228B 3937E498".
Definition b := hS2N "63E4C6D3 B23B0C84 9CF84241 484BFE48 F61D59A5 B16BA06E 6E12D1DA 27C5249A".
Definition xG := hS2N "421DEBD6 1B62EAB6 746434EB C3CC315E 32220B3B ADD50BDC 4C4E6C14 7FEDD43D".
Definition yG := hS2N "0680512B CBB42C07 D47349D2 153B70C4 E5D7FDFC BFA36EA1 A85841B9 E46E09A2". 
Definition n := hS2N "8542D69E 4C044F18 E8B92435 BF6FF7DD 29772063 0485628D 5AE74EE7 C32E79B7".
Definition h := 1.  (* By Hasse Thm *)
Definition M := hS2bL "656E63 72797074 696F6E20 7374616E 64617264".
Definition dB := hS2N "1649AB77 A00637BD 5E2EFE28 3FBF3535 34AA7F7C B89463F2 08DDBC29 20BB0DA0".
Definition xB := hS2N "435B39CC A8F3B508 C1488AFC 67BE491A 0F7BA07E 581A0E48 49A5CF70 628A7E0A".
Definition yB := hS2N "75DDBA78 F15FEECB 4C7895E2 C1CDF5FE 01DEBB2C DBADF453 99CCF77B BA076A42".
Definition k := hS2N "4C62EEFD 6ECFC2B9 5B92FD6C 3D957514 8AFA1742 5546D490 18E5388D 49DD7B4F".

Definition G := Cop (xG, yG).
Definition PB := Cop (xB, yB).
Definition klen := length M.  
(*
Time Compute match TryComputeTwithK k p a h ucp G PB klen Hash constant_v with
  | Error s => Error s
  | Normal None => Normal None
  | Normal (Some (a, b, c, d)) =>
      Normal (Some (bL2hS a, bL2hS b, bL2hS c, bL2hS d))
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

(*
Time Compute match ComputeCwithklist M [k] p a h  ucp (Cop (xG, yG)) (Cop (xB, yB)) Hash constant_v with
| Error s => Error s
| Normal bl => Normal (bL2hS bl)
end. 
= Normal
         "04245c26fb68b1ddddb12c4b6bf9f2b6d5fe60a383b0d18d1c4144abf17f6252e776cb9264c2a7e88e52b19903fdc47378f605e36811f5c07423a24b84400f01b8650053a89b41c418b0c3aad00d886c002864679c3d7360c30156fab7c80a0276712da9d8094a634b766d3a285e07480653426d"
     : optErr string
Finished transaction in 1239.021 secs (1237.408u,0.874s) (successful)
Correct
*)
Definition C := hS2bL "04245C26 FB68B1DD DDB12C4B 6BF9F2B6 D5FE60A3 83B0D18D 1C4144AB F17F6252 E776CB92 64C2A7E8 8E52B199 03FDC473 78F605E3 6811F5C0 7423A24B 84400F01 B8650053 A89B41C4 18B0C3AA D00D886C 00286467 9C3D7360 C30156FA B7C80A02 76712DA9 D8094A63 4B766D3A 285E0748 0653426D". 

(*
Time Compute match ComputeM' C p a b h dB ucp klen Hash constant_v with
| Error s => Error s
| Normal bl => Normal (bL2hS bl)
end. 
*)
(*
* = Normal "656e6372797074696f6e207374616e64617264"
     : optErr string
Finished transaction in 612.356 secs (611.425u,0.411s) (successful)
Correct
*)
End test. 


