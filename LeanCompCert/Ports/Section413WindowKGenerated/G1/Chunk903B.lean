import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk903A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk903B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk903A

def state06 : KState := ⟨⟨362487382913787412, 362487506502195065⟩, ⟨(-223314468947100264), (-215774394198893124)⟩, true⟩

def words05 : List Nat := [371285118294650695, 371285118274227750, 371285118351016587, 371285118411018430, 371285118480583701, 371285118551380964, 371285118620981673, 371285118624134654, 371285118556719488, 371285118587118883]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 90350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 90300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479080554628701, 362479204171162463⟩, ⟨526931986476913990, 534474602845553404⟩, true⟩

def words06 : List Nat := [371285118728497968, 371285118731651015, 371285118710089825, 371285118669322371, 371285118627382047, 371285118591336830, 371285118492861759, 371285118483884613, 371285118473821753, 371285118463547608]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 90360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 90300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496291990367349, 362496415635355034⟩, ⟨(-1028537728458146556), (-1020992540563111328)⟩, true⟩

def words07 : List Nat := [371285118457163918, 371285118517835357, 371285118699256400, 371285118735803518, 371285118751329860, 371285118767903402, 371285118834024396, 371285118840176626, 371285118967307514, 371285119095810627]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 90370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 90300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477723916965988, 362477847590414925⟩, ⟨649711831510945947, 657259591876748551⟩, true⟩

def words08 : List Nat := [371285119217715974, 371285119220869881, 371285119203159556, 371285119230781742, 371285119294216124, 371285119297371380, 371285119218114000, 371285119117942345, 371285119016533055, 371285118965477175]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 90380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 90300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472053374713338, 362472177076628840⟩, ⟨1162288961935332890, 1169839295536063038⟩, true⟩

def words09 : List Nat := [371285118887211405, 371285118839979272, 371285118791656904, 371285118736226281, 371285118516758837, 371285118323477191, 371285118128555781, 371285118057043838, 371285117916356752, 371285117776800700]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 90300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 90300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk903B
