import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk506A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk506B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk506A

def state06 : KState := ⟨⟨360615974851677434, 360615990969104073⟩, ⟨(-1722031907884401236), (-1721480193970401012)⟩, true⟩

def words05 : List Nat := [360582006379456744, 360582006670454970, 360582007194346554, 360582007744621714, 360582007910833267, 360582008077088553, 360582008561763860, 360582009243054761, 360582009914410666, 360582010585890746]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 50650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 50600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360623791127864580, 360623807251960239⟩, ⟨(-2118228114556555751), (-2117676062757316799)⟩, true⟩

def words06 : List Nat := [360582011008283466, 360582011162241527, 360582011527529953, 360582011893008652, 360582012160599421, 360582012662659346, 360582012969577118, 360582013276559358, 360582013762645610, 360582014588252057]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 50660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 50600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579987357299455, 360580003487997769⟩, ⟨101680667632285329, 102233054021067777⟩, true⟩

def words07 : List Nat := [360582015802274131, 360582017016382305, 360582017909337794, 360582018692043972, 360582019371825037, 360582020051764321, 360582020596599349, 360582020753230405, 360582020753860562, 360582020714793765]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 50670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 50600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605254891128962, 360605271028432389⟩, ⟨(-1178962437168057499), (-1178409715998458361)⟩, true⟩

def words08 : List Nat := [360582020893652770, 360582021308583603, 360582022111800546, 360582022915119835, 360582023410015352, 360582023516749126, 360582023517327958, 360582023455274107, 360582023647237579, 360582024106572524]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 50680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 50600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592151776232555, 360592167920208652⟩, ⟨(-514623357045982415), (-514070297607514627)⟩, true⟩

def words09 : List Nat := [360582024334663187, 360582024562824263, 360582025088587175, 360582025976230540, 360582026766144717, 360582027556141990, 360582028104691243, 360582028265240037, 360582028465803492, 360582028666592205]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 50690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 50600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 50600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk506B
