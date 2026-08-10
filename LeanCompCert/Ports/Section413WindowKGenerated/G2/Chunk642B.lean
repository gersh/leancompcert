import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk642A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk642B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk642A

def state06 : KState := ⟨⟨360574448360845160, 360574474794123094⟩, ⟨539472307919288543, 540619744454047963⟩, true⟩

def words05 : List Nat := [360582888204363141, 360582888234036947, 360582888234780751, 360582888284557298, 360582888285314039, 360582888274374659, 360582888263337087, 360582888130712362, 360582887929655664, 360582887799794648]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 64250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 64200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360579950591196889, 360579977032979182⟩, ⟨185931701367869132, 187079684436752854⟩, true⟩

def words06 : List Nat := [360582887734407783, 360582887868578007, 360582887869384188, 360582887869984219, 360582887870436067, 360582887869290876, 360582887923037656, 360582887976943108, 360582887977756692, 360582887872942412]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 64260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 64200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606559322244210, 360606585772561671⟩, ⟨(-1524359875116779603), (-1523211343449378255)⟩, true⟩

def words07 : List Nat := [360582888024928086, 360582888222467657, 360582888457139204, 360582888698126747, 360582888730912342, 360582888763766325, 360582888769331801, 360582888897211738, 360582889266593786, 360582889636169123]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 64270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 64200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582482703354925, 360582509162295501⟩, ⟨23264214105206802, 24413300109238418⟩, true⟩

def words08 : List Nat := [360582889819911028, 360582889820815398, 360582889947329061, 360582890132099984, 360582890132861969, 360582890118955749, 360582889864067003, 360582889487398718, 360582889110552897, 360582888899425837]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 64280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 64200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360572767593078541, 360572794060538156⟩, ⟨647949167569213758, 649098801304266406⟩, true⟩

def words09 : List Nat := [360582889080264827, 360582889267177671, 360582889305010490, 360582889374119265, 360582889374894855, 360582889219206048, 360582889099523195, 360582889100432230, 360582889065764058, 360582888909703075]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 64290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 64200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 64200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk642B
