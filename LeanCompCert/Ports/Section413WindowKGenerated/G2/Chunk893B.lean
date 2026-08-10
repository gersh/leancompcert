import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk893A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk893B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk893A

def state06 : KState := ⟨⟨360580215788618066, 360580268247661166⟩, ⟨156043146166398688, 159208714148104058⟩, true⟩

def words05 : List Nat := [360582051025041145, 360582050964294352, 360582050903160044, 360582050861570027, 360582050740530049, 360582050490536506, 360582050240303707, 360582050045708664, 360582049921526439, 360582049902922448]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 89350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 89300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574384019573126, 360574436490917967⟩, ⟨677204794141353227, 680371461466564113⟩, true⟩

def words06 : List Nat := [360582049884143769, 360582049803410516, 360582049868811595, 360582049964937845, 360582050012867961, 360582050014156817, 360582049937098891, 360582049797381248, 360582049657440791, 360582049464639200]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 89360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 89300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360563442006137318, 360563494489620728⟩, ⟨1655168712370485384, 1658336464579889092⟩, true⟩

def words07 : List Nat := [360582049420334640, 360582049461460193, 360582049462609459, 360582049434657143, 360582049281469153, 360582049025748458, 360582048769626621, 360582048615847223, 360582048471487341, 360582048265236973]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 89370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 89300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360599424215182075, 360599476710850779⟩, ⟨(-1561139881643587662), (-1557971040252490538)⟩, true⟩

def words08 : List Nat := [360582048058698106, 360582047977534242, 360582047958783337, 360582047929317680, 360582047899752933, 360582047750454127, 360582047662301859, 360582047681634450, 360582047790819155, 360582047987150938]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 89380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 89300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360594487931376959, 360594540439311716⟩, ⟨(-1119846681461592013), (-1116676743548369569)⟩, true⟩

def words09 : List Nat := [360582048114552762, 360582048242092983, 360582048494343766, 360582048818808255, 360582049083676854, 360582049348747665, 360582049489702672, 360582049505762408, 360582049646524136, 360582049787713319]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 89390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 89300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 89300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk893B
