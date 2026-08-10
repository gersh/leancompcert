import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk740A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk740B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk740A

def state06 : KState := ⟨⟨362482820074009925, 362482901832278523⟩, ⟨172033728935936169, 176122816817103491⟩, true⟩

def words05 : List Nat := [371285281096377552, 371285281040038453, 371285280982381845, 371285280976534317, 371285280753088961, 371285280500309182, 371285280246477372, 371285280155097563, 371285279971367735, 371285279942146429]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 74050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 74000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362467264738870528, 362467346520117799⟩, ⟨1324111896656343981, 1328202686458139357⟩, true⟩

def words06 : List Nat := [371285279911968141, 371285279877638313, 371285279653670357, 371285279525257019, 371285279395553487, 371285279322327019, 371285279050953155, 371285278743134969, 371285278434316576, 371285278242629723]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 74060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 74000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475794949430779, 362475876753620070⟩, ⟨692311564420787379, 696404053656322295⟩, true⟩

def words07 : List Nat := [371285278002268277, 371285277944968986, 371285277886787550, 371285277829752610, 371285277710227556, 371285277648162976, 371285277701696380, 371285277704242974, 371285277580291268, 371285277456288217]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 74070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 74000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474353980946930, 362474435807972475⟩, ⟨799069038097661258, 803163219155698358⟩, true⟩

def words08 : List Nat := [371285277331151753, 371285277251897827, 371285277080357631, 371285277039244334, 371285276997375472, 371285276904608687, 371285276624261415, 371285276426464566, 371285276227244141, 371285276180750930]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 74080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 74000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476491116895034, 362476572967089043⟩, ⟨640737279194196577, 644833176918252785⟩, true⟩

def words09 : List Nat := [371285276036343239, 371285275893204966, 371285275785073450, 371285275787881093, 371285275741817499, 371285275688956924, 371285275635202875, 371285275581069791, 371285275283494816, 371285275169206699]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 74090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 74000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 74000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk740B
