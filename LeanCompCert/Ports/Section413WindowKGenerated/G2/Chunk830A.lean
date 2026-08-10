import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk830A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603407112004548, 360603452111628621⟩, ⟨(-1748527296955596052), (-1746004894937364488)⟩, true⟩

def state01 : KState := ⟨⟨360614616679304022, 360614661690256174⟩, ⟨(-2679095204639312570), (-2676571862333706936)⟩, true⟩

def words00 : List Nat := [360582416335137628, 360582416411741944, 360582416633206247, 360582416855014801, 360582416995829437, 360582417210331701, 360582417331846316, 360582417453476274, 360582417719950736, 360582418109738729]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584052706877254, 360584097729058084⟩, ⟨(-141850951242770364), (-139326676788354880)⟩, true⟩

def words01 : List Nat := [360582418480520765, 360582418851517281, 360582419090841151, 360582419185548784, 360582419243542081, 360582419301862027, 360582419381989293, 360582419476261165, 360582419497536934, 360582419519005347]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602158523420485, 360602203556836355⟩, ⟨(-1645064782659072033), (-1642539575419480083)⟩, true⟩

def words02 : List Nat := [360582419642156052, 360582419853998812, 360582420210505485, 360582420567231734, 360582420790701750, 360582420869547708, 360582420900533177, 360582420931863114, 360582421072455676, 360582421311946863]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591404870136573, 360591449914886781⟩, ⟨(-752099957474465005), (-749573809087516351)⟩, true⟩

def words03 : List Nat := [360582421459326890, 360582421606828313, 360582421846468015, 360582422196927811, 360582422510551286, 360582422824361474, 360582423056602487, 360582423144304502, 360582423253977585, 360582423364037352]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584437444121616, 360584482500103459⟩, ⟨(-173580658905574993), (-171053577787055575)⟩, true⟩

def words04 : List Nat := [360582423469812635, 360582423471003501, 360582423432211578, 360582423320936869, 360582423209467683, 360582423012866252, 360582422907966561, 360582422928714610, 360582422929779219, 360582422879174307]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk830A
