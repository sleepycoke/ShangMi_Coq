Require Import NArith.
Require Import Coq.PArith.BinPosDef. 
Require Import Coq.Strings.HexString. 
Require Import Ascii String. 
Require Import Coq.Strings.Ascii. 
Require Import Coq.Strings.String.

Definition Sbox (n : N) : N := 
  if N.eqb n (to_N "0x0") then (to_N "0xd6") else
  if N.eqb n (to_N "0x1") then (to_N "0x90") else
  if N.eqb n (to_N "0x2") then (to_N "0xe9") else
  if N.eqb n (to_N "0x3") then (to_N "0xfe") else
  if N.eqb n (to_N "0x4") then (to_N "0xcc") else
  if N.eqb n (to_N "0x5") then (to_N "0xe1") else
  if N.eqb n (to_N "0x6") then (to_N "0x3d") else
  if N.eqb n (to_N "0x7") then (to_N "0xb7") else
  if N.eqb n (to_N "0x8") then (to_N "0x16") else
  if N.eqb n (to_N "0x9") then (to_N "0xb6") else
  if N.eqb n (to_N "0xa") then (to_N "0x14") else
  if N.eqb n (to_N "0xb") then (to_N "0xc2") else
  if N.eqb n (to_N "0xc") then (to_N "0x28") else
  if N.eqb n (to_N "0xd") then (to_N "0xfb") else
  if N.eqb n (to_N "0xe") then (to_N "0x2c") else
  if N.eqb n (to_N "0xf") then (to_N "0x05") else
  if N.eqb n (to_N "0x10") then (to_N "0x2b") else
  if N.eqb n (to_N "0x11") then (to_N "0x67") else
  if N.eqb n (to_N "0x12") then (to_N "0x9a") else
  if N.eqb n (to_N "0x13") then (to_N "0x76") else
  if N.eqb n (to_N "0x14") then (to_N "0x2a") else
  if N.eqb n (to_N "0x15") then (to_N "0xbe") else
  if N.eqb n (to_N "0x16") then (to_N "0x04") else
  if N.eqb n (to_N "0x17") then (to_N "0xc3") else
  if N.eqb n (to_N "0x18") then (to_N "0xaa") else
  if N.eqb n (to_N "0x19") then (to_N "0x44") else
  if N.eqb n (to_N "0x1a") then (to_N "0x13") else
  if N.eqb n (to_N "0x1b") then (to_N "0x26") else
  if N.eqb n (to_N "0x1c") then (to_N "0x49") else
  if N.eqb n (to_N "0x1d") then (to_N "0x86") else
  if N.eqb n (to_N "0x1e") then (to_N "0x06") else
  if N.eqb n (to_N "0x1f") then (to_N "0x99") else
  if N.eqb n (to_N "0x20") then (to_N "0x9c") else
  if N.eqb n (to_N "0x21") then (to_N "0x42") else
  if N.eqb n (to_N "0x22") then (to_N "0x50") else
  if N.eqb n (to_N "0x23") then (to_N "0xf4") else
  if N.eqb n (to_N "0x24") then (to_N "0x91") else
  if N.eqb n (to_N "0x25") then (to_N "0xef") else
  if N.eqb n (to_N "0x26") then (to_N "0x98") else
  if N.eqb n (to_N "0x27") then (to_N "0x7a") else
  if N.eqb n (to_N "0x28") then (to_N "0x33") else
  if N.eqb n (to_N "0x29") then (to_N "0x54") else
  if N.eqb n (to_N "0x2a") then (to_N "0x0b") else
  if N.eqb n (to_N "0x2b") then (to_N "0x43") else
  if N.eqb n (to_N "0x2c") then (to_N "0xed") else
  if N.eqb n (to_N "0x2d") then (to_N "0xcf") else
  if N.eqb n (to_N "0x2e") then (to_N "0xac") else
  if N.eqb n (to_N "0x2f") then (to_N "0x62") else
  if N.eqb n (to_N "0x30") then (to_N "0xe4") else
  if N.eqb n (to_N "0x31") then (to_N "0xb3") else
  if N.eqb n (to_N "0x32") then (to_N "0x1c") else
  if N.eqb n (to_N "0x33") then (to_N "0xa9") else
  if N.eqb n (to_N "0x34") then (to_N "0xc9") else
  if N.eqb n (to_N "0x35") then (to_N "0x08") else
  if N.eqb n (to_N "0x36") then (to_N "0xe8") else
  if N.eqb n (to_N "0x37") then (to_N "0x95") else
  if N.eqb n (to_N "0x38") then (to_N "0x80") else
  if N.eqb n (to_N "0x39") then (to_N "0xdf") else
  if N.eqb n (to_N "0x3a") then (to_N "0x94") else
  if N.eqb n (to_N "0x3b") then (to_N "0xfa") else
  if N.eqb n (to_N "0x3c") then (to_N "0x75") else
  if N.eqb n (to_N "0x3d") then (to_N "0x8f") else
  if N.eqb n (to_N "0x3e") then (to_N "0x3f") else
  if N.eqb n (to_N "0x3f") then (to_N "0xa6") else
  if N.eqb n (to_N "0x40") then (to_N "0x47") else
  if N.eqb n (to_N "0x41") then (to_N "0x07") else
  if N.eqb n (to_N "0x42") then (to_N "0xa7") else
  if N.eqb n (to_N "0x43") then (to_N "0xfc") else
  if N.eqb n (to_N "0x44") then (to_N "0xf3") else
  if N.eqb n (to_N "0x45") then (to_N "0x73") else
  if N.eqb n (to_N "0x46") then (to_N "0x17") else
  if N.eqb n (to_N "0x47") then (to_N "0xba") else
  if N.eqb n (to_N "0x48") then (to_N "0x83") else
  if N.eqb n (to_N "0x49") then (to_N "0x59") else
  if N.eqb n (to_N "0x4a") then (to_N "0x3c") else
  if N.eqb n (to_N "0x4b") then (to_N "0x19") else
  if N.eqb n (to_N "0x4c") then (to_N "0xe6") else
  if N.eqb n (to_N "0x4d") then (to_N "0x85") else
  if N.eqb n (to_N "0x4e") then (to_N "0x4f") else
  if N.eqb n (to_N "0x4f") then (to_N "0xa8") else
  if N.eqb n (to_N "0x50") then (to_N "0x68") else
  if N.eqb n (to_N "0x51") then (to_N "0x6b") else
  if N.eqb n (to_N "0x52") then (to_N "0x81") else
  if N.eqb n (to_N "0x53") then (to_N "0xb2") else
  if N.eqb n (to_N "0x54") then (to_N "0x71") else
  if N.eqb n (to_N "0x55") then (to_N "0x64") else
  if N.eqb n (to_N "0x56") then (to_N "0xda") else
  if N.eqb n (to_N "0x57") then (to_N "0x8b") else
  if N.eqb n (to_N "0x58") then (to_N "0xf8") else
  if N.eqb n (to_N "0x59") then (to_N "0xeb") else
  if N.eqb n (to_N "0x5a") then (to_N "0x0f") else
  if N.eqb n (to_N "0x5b") then (to_N "0x4b") else
  if N.eqb n (to_N "0x5c") then (to_N "0x70") else
  if N.eqb n (to_N "0x5d") then (to_N "0x56") else
  if N.eqb n (to_N "0x5e") then (to_N "0x9d") else
  if N.eqb n (to_N "0x5f") then (to_N "0x35") else
  if N.eqb n (to_N "0x60") then (to_N "0x1e") else
  if N.eqb n (to_N "0x61") then (to_N "0x24") else
  if N.eqb n (to_N "0x62") then (to_N "0x0e") else
  if N.eqb n (to_N "0x63") then (to_N "0x5e") else
  if N.eqb n (to_N "0x64") then (to_N "0x63") else
  if N.eqb n (to_N "0x65") then (to_N "0x58") else
  if N.eqb n (to_N "0x66") then (to_N "0xd1") else
  if N.eqb n (to_N "0x67") then (to_N "0xa2") else
  if N.eqb n (to_N "0x68") then (to_N "0x25") else
  if N.eqb n (to_N "0x69") then (to_N "0x22") else
  if N.eqb n (to_N "0x6a") then (to_N "0x7c") else
  if N.eqb n (to_N "0x6b") then (to_N "0x3b") else
  if N.eqb n (to_N "0x6c") then (to_N "0x01") else
  if N.eqb n (to_N "0x6d") then (to_N "0x21") else
  if N.eqb n (to_N "0x6e") then (to_N "0x78") else
  if N.eqb n (to_N "0x6f") then (to_N "0x87") else
  if N.eqb n (to_N "0x70") then (to_N "0xd4") else
  if N.eqb n (to_N "0x71") then (to_N "0x00") else
  if N.eqb n (to_N "0x72") then (to_N "0x46") else
  if N.eqb n (to_N "0x73") then (to_N "0x57") else
  if N.eqb n (to_N "0x74") then (to_N "0x9f") else
  if N.eqb n (to_N "0x75") then (to_N "0xd3") else
  if N.eqb n (to_N "0x76") then (to_N "0x27") else
  if N.eqb n (to_N "0x77") then (to_N "0x52") else
  if N.eqb n (to_N "0x78") then (to_N "0x4c") else
  if N.eqb n (to_N "0x79") then (to_N "0x36") else
  if N.eqb n (to_N "0x7a") then (to_N "0x02") else
  if N.eqb n (to_N "0x7b") then (to_N "0xe7") else
  if N.eqb n (to_N "0x7c") then (to_N "0xa0") else
  if N.eqb n (to_N "0x7d") then (to_N "0xc4") else
  if N.eqb n (to_N "0x7e") then (to_N "0xc8") else
  if N.eqb n (to_N "0x7f") then (to_N "0x9e") else
  if N.eqb n (to_N "0x80") then (to_N "0xea") else
  if N.eqb n (to_N "0x81") then (to_N "0xbf") else
  if N.eqb n (to_N "0x82") then (to_N "0x8a") else
  if N.eqb n (to_N "0x83") then (to_N "0xd2") else
  if N.eqb n (to_N "0x84") then (to_N "0x40") else
  if N.eqb n (to_N "0x85") then (to_N "0xc7") else
  if N.eqb n (to_N "0x86") then (to_N "0x38") else
  if N.eqb n (to_N "0x87") then (to_N "0xb5") else
  if N.eqb n (to_N "0x88") then (to_N "0xa3") else
  if N.eqb n (to_N "0x89") then (to_N "0xf7") else
  if N.eqb n (to_N "0x8a") then (to_N "0xf2") else
  if N.eqb n (to_N "0x8b") then (to_N "0xce") else
  if N.eqb n (to_N "0x8c") then (to_N "0xf9") else
  if N.eqb n (to_N "0x8d") then (to_N "0x61") else
  if N.eqb n (to_N "0x8e") then (to_N "0x15") else
  if N.eqb n (to_N "0x8f") then (to_N "0xa1") else
  if N.eqb n (to_N "0x90") then (to_N "0xe0") else
  if N.eqb n (to_N "0x91") then (to_N "0xae") else
  if N.eqb n (to_N "0x92") then (to_N "0x5d") else
  if N.eqb n (to_N "0x93") then (to_N "0xa4") else
  if N.eqb n (to_N "0x94") then (to_N "0x9b") else
  if N.eqb n (to_N "0x95") then (to_N "0x34") else
  if N.eqb n (to_N "0x96") then (to_N "0x1a") else
  if N.eqb n (to_N "0x97") then (to_N "0x55") else
  if N.eqb n (to_N "0x98") then (to_N "0xad") else
  if N.eqb n (to_N "0x99") then (to_N "0x93") else
  if N.eqb n (to_N "0x9a") then (to_N "0x32") else
  if N.eqb n (to_N "0x9b") then (to_N "0x30") else
  if N.eqb n (to_N "0x9c") then (to_N "0xf5") else
  if N.eqb n (to_N "0x9d") then (to_N "0x8c") else
  if N.eqb n (to_N "0x9e") then (to_N "0xb1") else
  if N.eqb n (to_N "0x9f") then (to_N "0xe3") else
  if N.eqb n (to_N "0xa0") then (to_N "0x1d") else
  if N.eqb n (to_N "0xa1") then (to_N "0xf6") else
  if N.eqb n (to_N "0xa2") then (to_N "0xe2") else
  if N.eqb n (to_N "0xa3") then (to_N "0x2e") else
  if N.eqb n (to_N "0xa4") then (to_N "0x82") else
  if N.eqb n (to_N "0xa5") then (to_N "0x66") else
  if N.eqb n (to_N "0xa6") then (to_N "0xca") else
  if N.eqb n (to_N "0xa7") then (to_N "0x60") else
  if N.eqb n (to_N "0xa8") then (to_N "0xc0") else
  if N.eqb n (to_N "0xa9") then (to_N "0x29") else
  if N.eqb n (to_N "0xaa") then (to_N "0x23") else
  if N.eqb n (to_N "0xab") then (to_N "0xab") else
  if N.eqb n (to_N "0xac") then (to_N "0x0d") else
  if N.eqb n (to_N "0xad") then (to_N "0x53") else
  if N.eqb n (to_N "0xae") then (to_N "0x4e") else
  if N.eqb n (to_N "0xaf") then (to_N "0x6f") else
  if N.eqb n (to_N "0xb0") then (to_N "0xd5") else
  if N.eqb n (to_N "0xb1") then (to_N "0xdb") else
  if N.eqb n (to_N "0xb2") then (to_N "0x37") else
  if N.eqb n (to_N "0xb3") then (to_N "0x45") else
  if N.eqb n (to_N "0xb4") then (to_N "0xde") else
  if N.eqb n (to_N "0xb5") then (to_N "0xfd") else
  if N.eqb n (to_N "0xb6") then (to_N "0x8e") else
  if N.eqb n (to_N "0xb7") then (to_N "0x2f") else
  if N.eqb n (to_N "0xb8") then (to_N "0x03") else
  if N.eqb n (to_N "0xb9") then (to_N "0xff") else
  if N.eqb n (to_N "0xba") then (to_N "0x6a") else
  if N.eqb n (to_N "0xbb") then (to_N "0x72") else
  if N.eqb n (to_N "0xbc") then (to_N "0x6d") else
  if N.eqb n (to_N "0xbd") then (to_N "0x6c") else
  if N.eqb n (to_N "0xbe") then (to_N "0x5b") else
  if N.eqb n (to_N "0xbf") then (to_N "0x51") else
  if N.eqb n (to_N "0xc0") then (to_N "0x8d") else
  if N.eqb n (to_N "0xc1") then (to_N "0x1b") else
  if N.eqb n (to_N "0xc2") then (to_N "0xaf") else
  if N.eqb n (to_N "0xc3") then (to_N "0x92") else
  if N.eqb n (to_N "0xc4") then (to_N "0xbb") else
  if N.eqb n (to_N "0xc5") then (to_N "0xdd") else
  if N.eqb n (to_N "0xc6") then (to_N "0xbc") else
  if N.eqb n (to_N "0xc7") then (to_N "0x7f") else
  if N.eqb n (to_N "0xc8") then (to_N "0x11") else
  if N.eqb n (to_N "0xc9") then (to_N "0xd9") else
  if N.eqb n (to_N "0xca") then (to_N "0x5c") else
  if N.eqb n (to_N "0xcb") then (to_N "0x41") else
  if N.eqb n (to_N "0xcc") then (to_N "0x1f") else
  if N.eqb n (to_N "0xcd") then (to_N "0x10") else
  if N.eqb n (to_N "0xce") then (to_N "0x5a") else
  if N.eqb n (to_N "0xcf") then (to_N "0xd8") else
  if N.eqb n (to_N "0xd0") then (to_N "0x0a") else
  if N.eqb n (to_N "0xd1") then (to_N "0xc1") else
  if N.eqb n (to_N "0xd2") then (to_N "0x31") else
  if N.eqb n (to_N "0xd3") then (to_N "0x88") else
  if N.eqb n (to_N "0xd4") then (to_N "0xa5") else
  if N.eqb n (to_N "0xd5") then (to_N "0xcd") else
  if N.eqb n (to_N "0xd6") then (to_N "0x7b") else
  if N.eqb n (to_N "0xd7") then (to_N "0xbd") else
  if N.eqb n (to_N "0xd8") then (to_N "0x2d") else
  if N.eqb n (to_N "0xd9") then (to_N "0x74") else
  if N.eqb n (to_N "0xda") then (to_N "0xd0") else
  if N.eqb n (to_N "0xdb") then (to_N "0x12") else
  if N.eqb n (to_N "0xdc") then (to_N "0xb8") else
  if N.eqb n (to_N "0xdd") then (to_N "0xe5") else
  if N.eqb n (to_N "0xde") then (to_N "0xb4") else
  if N.eqb n (to_N "0xdf") then (to_N "0xb0") else
  if N.eqb n (to_N "0xe0") then (to_N "0x89") else
  if N.eqb n (to_N "0xe1") then (to_N "0x69") else
  if N.eqb n (to_N "0xe2") then (to_N "0x97") else
  if N.eqb n (to_N "0xe3") then (to_N "0x4a") else
  if N.eqb n (to_N "0xe4") then (to_N "0x0c") else
  if N.eqb n (to_N "0xe5") then (to_N "0x96") else
  if N.eqb n (to_N "0xe6") then (to_N "0x77") else
  if N.eqb n (to_N "0xe7") then (to_N "0x7e") else
  if N.eqb n (to_N "0xe8") then (to_N "0x65") else
  if N.eqb n (to_N "0xe9") then (to_N "0xb9") else
  if N.eqb n (to_N "0xea") then (to_N "0xf1") else
  if N.eqb n (to_N "0xeb") then (to_N "0x09") else
  if N.eqb n (to_N "0xec") then (to_N "0xc5") else
  if N.eqb n (to_N "0xed") then (to_N "0x6e") else
  if N.eqb n (to_N "0xee") then (to_N "0xc6") else
  if N.eqb n (to_N "0xef") then (to_N "0x84") else
  if N.eqb n (to_N "0xf0") then (to_N "0x18") else
  if N.eqb n (to_N "0xf1") then (to_N "0xf0") else
  if N.eqb n (to_N "0xf2") then (to_N "0x7d") else
  if N.eqb n (to_N "0xf3") then (to_N "0xec") else
  if N.eqb n (to_N "0xf4") then (to_N "0x3a") else
  if N.eqb n (to_N "0xf5") then (to_N "0xdc") else
  if N.eqb n (to_N "0xf6") then (to_N "0x4d") else
  if N.eqb n (to_N "0xf7") then (to_N "0x20") else
  if N.eqb n (to_N "0xf8") then (to_N "0x79") else
  if N.eqb n (to_N "0xf9") then (to_N "0xee") else
  if N.eqb n (to_N "0xfa") then (to_N "0x5f") else
  if N.eqb n (to_N "0xfb") then (to_N "0x3e") else
  if N.eqb n (to_N "0xfc") then (to_N "0xd7") else
  if N.eqb n (to_N "0xfd") then (to_N "0xcb") else
  if N.eqb n (to_N "0xfe") then (to_N "0x39") else
  (to_N "0x48"). 
 

Definition FK (i : N) : N :=
  if N.eqb i 0 then to_N("0xA3B1BAC6") else
  if N.eqb i 1 then to_N("0x56AA3350") else
  if N.eqb i 2 then to_N("0x677D9197") else
  to_N("0xB27022DC"). 

Definition CK (i : N) : N :=
  if N.eqb i 0 then to_N("0x00070e15") else
  if N.eqb i 1 then to_N("0x1c232a31") else
  if N.eqb i 2 then to_N("0x383f464d") else
  if N.eqb i 3 then to_N("0x545b6269") else
  if N.eqb i 4 then to_N("0x70777e85") else
  if N.eqb i 5 then to_N("0x8c939aa1") else
  if N.eqb i 6 then to_N("0xa8afb6bd") else
  if N.eqb i 7 then to_N("0xc4cbd2d9") else
  if N.eqb i 8 then to_N("0xe0e7eef5") else
  if N.eqb i 9 then to_N("0xfc030a11") else
  if N.eqb i 10 then to_N("0x181f262d") else
  if N.eqb i 11 then to_N("0x343b4249") else
  if N.eqb i 12 then to_N("0x50575e65") else
  if N.eqb i 13 then to_N("0x6c737a81") else
  if N.eqb i 14 then to_N("0x888f969d") else
  if N.eqb i 15 then to_N("0xa4abb2b9") else
  if N.eqb i 16 then to_N("0xc0c7ced5") else
  if N.eqb i 17 then to_N("0xdce3eaf1") else
  if N.eqb i 18 then to_N("0xf8ff060d") else
  if N.eqb i 19 then to_N("0x141b2229") else
  if N.eqb i 20 then to_N("0x30373e45") else
  if N.eqb i 21 then to_N("0x4c535a61") else
  if N.eqb i 22 then to_N("0x686f767d") else
  if N.eqb i 23 then to_N("0x848b9299") else
  if N.eqb i 24 then to_N("0xa0a7aeb5") else
  if N.eqb i 25 then to_N("0xbcc3cad1") else
  if N.eqb i 26 then to_N("0xd8dfe6ed") else
  if N.eqb i 27 then to_N("0xf4fb0209") else
  if N.eqb i 28 then to_N("0x10171e25") else
  if N.eqb i 29 then to_N("0x2c333a41") else
  if N.eqb i 30 then to_N("0x484f565d") else
  to_N("0x646b7279"). 

