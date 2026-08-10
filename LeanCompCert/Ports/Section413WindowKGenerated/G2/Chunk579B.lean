import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk579A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk579B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk579A

def state06 : KState := ⟨⟨360570199238189896, 360570220566698249⟩, ⟨678392730072713848, 679227915670326998⟩, true⟩

def words05 : List Nat := [360581938710599159, 360581938976048989, 360581939116278883, 360581939444737808, 360581939651699031, 360581939858784965, 360581939915559127, 360581939916368256, 360581939676080556, 360581939474836109]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 57950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 57900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360565096170593640, 360565117506719025⟩, ⟨974158183634856481, 974993810752753985⟩, true⟩

def words06 : List Nat := [360581939302289662, 360581939303098926, 360581939121677641, 360581938785029342, 360581938448260438, 360581938035534972, 360581937771309907, 360581937388735890, 360581937006095805, 360581936444285918]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 57960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 57900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360619574244573289, 360619595588330240⟩, ⟨(-2184231032466908377), (-2183394962908607573)⟩, true⟩

def words07 : List Nat := [360581936154814053, 360581936023420492, 360581936057133498, 360581936342145148, 360581936372783407, 360581936403482829, 360581936731610799, 360581937211164975, 360581937861325987, 360581938511651525]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 57970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 57900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360598249438246110, 360598270789718413⟩, ⟨(-947884776487142420), (-947048259554578194)⟩, true⟩

def words08 : List Nat := [360581938876365092, 360581939046549963, 360581939353926125, 360581939661528140, 360581939892871309, 360581939912748780, 360581939913478638, 360581939720540208, 360581939554797140, 360581939837336931]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 57980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 57900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571411312890724, 360571432671983322⟩, ⟨608672065314417176, 609509024186479858⟩, true⟩

def words09 : List Nat := [360581940417004951, 360581940996813452, 360581941388226393, 360581941557650864, 360581941558340204, 360581941526264517, 360581941658348989, 360581941659158922, 360581941628611536, 360581941448262400]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 57990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 57900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 57900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk579B
