import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk971A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491768477425336, 362491911985685814⟩, ⟨(-648249045474472257), (-638841016670116363)⟩, true⟩

def state01 : KState := ⟨⟨362487550358061299, 362487693897121324⟩, ⟨(-238674541654576683), (-229263522064193853)⟩, true⟩

def words00 : List Nat := [371285332916912758, 371285332920321326, 371285332921488245, 371285332978207039, 371285333065005213, 371285333068417737, 371285333040691611, 371285333013777625, 371285333028981933, 371285333057236407]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 97100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 97100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482393491839458, 362482537061617635⟩, ⟨262148383845244572, 271562386635176104⟩, true⟩

def words01 : List Nat := [371285333127825847, 371285333199792608, 371285333270251113, 371285333273659550, 371285333215683634, 371285333191261727, 371285333242777713, 371285333246246123, 371285333239604715, 371285333214692545]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 97110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 97100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481237651429666, 362481381251705766⟩, ⟨374414478612250099, 383831443514924107⟩, true⟩

def words02 : List Nat := [371285333205265520, 371285333209021344, 371285333196735434, 371285333221590335, 371285333224277879, 371285333215626620, 371285333064541981, 371285333021422888, 371285332977212427, 371285332980764913]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 97120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 97100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481670380450660, 362481814011754275⟩, ⟨332407269634237639, 341827248401437719⟩, true⟩

def words03 : List Nat := [371285332942627402, 371285332905348796, 371285332921338088, 371285332926951282, 371285332963102046, 371285333000621512, 371285333031583874, 371285333035001705, 371285332957202164, 371285332925161743]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 97130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 97100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474989394973851, 362475133056627821⟩, ⟨981422112346864456, 990845039503981910⟩, true⟩

def words04 : List Nat := [371285332909261910, 371285332912670598, 371285332791929577, 371285332672059639, 371285332550855020, 371285332463032408, 371285332335364434, 371285332286892521, 371285332237313935, 371285332182098784]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 97140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 97100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk971A
