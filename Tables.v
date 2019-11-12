Require Import NArith.
Require Import Coq.PArith.BinPosDef. 
Require Import Coq.Strings.HexString. 
Require Import Ascii String. 
Require Import Coq.Strings.Ascii. 
Require Import Coq.Strings.String.
Import Coq.Lists.List.
Import ListNotations. 
Open Scope list_scope.
Open Scope string_scope.
Open Scope N_scope.
Definition boxlist :=
 [["d6";"90";"e9";"fe";"cc";"e1";"3d";"b7";"16";"b6";"14";"c2";"28";"fb";"2c";"05"];
  ["2b";"67";"9a";"76";"2a";"be";"04";"c3";"aa";"44";"13";"26";"49";"86";"06";"99"];
  ["9c";"42";"50";"f4";"91";"ef";"98";"7a";"33";"54";"0b";"43";"ed";"cf";"ac";"62"];
  ["e4";"b3";"1c";"a9";"c9";"08";"e8";"95";"80";"df";"94";"fa";"75";"8f";"3f";"a6"];
  ["47";"07";"a7";"fc";"f3";"73";"17";"ba";"83";"59";"3c";"19";"e6";"85";"4f";"a8"];
  ["68";"6b";"81";"b2";"71";"64";"da";"8b";"f8";"eb";"0f";"4b";"70";"56";"9d";"35"];
  ["1e";"24";"0e";"5e";"63";"58";"d1";"a2";"25";"22";"7c";"3b";"01";"21";"78";"87"];
  ["d4";"00";"46";"57";"9f";"d3";"27";"52";"4c";"36";"02";"e7";"a0";"c4";"c8";"9e"];
  ["ea";"bf";"8a";"d2";"40";"c7";"38";"b5";"a3";"f7";"f2";"ce";"f9";"61";"15";"a1"];
  ["e0";"ae";"5d";"a4";"9b";"34";"1a";"55";"ad";"93";"32";"30";"f5";"8c";"b1";"e3"];
  ["1d";"f6";"e2";"2e";"82";"66";"ca";"60";"c0";"29";"23";"ab";"0d";"53";"4e";"6f"];
  ["d5";"db";"37";"45";"de";"fd";"8e";"2f";"03";"ff";"6a";"72";"6d";"6c";"5b";"51"];
  ["8d";"1b";"af";"92";"bb";"dd";"bc";"7f";"11";"d9";"5c";"41";"1f";"10";"5a";"d8"];
  ["0a";"c1";"31";"88";"a5";"cd";"7b";"bd";"2d";"74";"d0";"12";"b8";"e5";"b4";"b0"];
  ["89";"69";"97";"4a";"0c";"96";"77";"7e";"65";"b9";"f1";"09";"c5";"6e";"c6";"84"];
  ["18";"f0";"7d";"ec";"3a";"dc";"4d";"20";"79";"ee";"5f";"3e";"d7";"cb";"39";"48"]].

Definition Sbox (n : N) : N :=
  HexString.to_N ("0x" ++ (nth (N.to_nat (N.modulo n 16)) (nth (N.to_nat (N.div n 16)) boxlist []) "")). 
 
Definition FKlist := ["A3B1BAC6"; "56AA3350"; "677D9197"; "B27022DC"].

Definition FK (n : N) : N :=
  HexString.to_N ("0x" ++ (nth (N.to_nat n) FKlist "")). 
 
Definition CKlist := 
 ["00070e15"; "1c232a31"; "383f464d"; "545b6269";
  "70777e85"; "8c939aa1"; "a8afb6bd"; "c4cbd2d9";
  "e0e7eef5"; "fc030a11"; "181f262d"; "343b4249";
  "50575e65"; "6c737a81"; "888f969d"; "a4abb2b9";
  "c0c7ced5"; "dce3eaf1"; "f8ff060d"; "141b2229";
  "30373e45"; "4c535a61"; "686f767d"; "848b9299";
  "a0a7aeb5"; "bcc3cad1"; "d8dfe6ed"; "f4fb0209";
  "10171e25"; "2c333a41"; "484f565d"; "646b7279"]. 

Definition CK (n : N) : N :=
  HexString.to_N ("0x" ++ (nth (N.to_nat n) CKlist "")). 

Definition constant_v := 256%nat. (*According to the examples. *)

