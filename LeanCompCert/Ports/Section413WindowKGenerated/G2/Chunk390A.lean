import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk390A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586979250674025, 360586988600278907⟩, ⟨(-180956936863205031), (-180710475340606289)⟩, true⟩

def state01 : KState := ⟨⟨360580798871050402, 360580808225619336⟩, ⟨60024057124425573, 60270712269593423⟩, true⟩

def words00 : List Nat := [360582355645425017, 360582355645952377, 360582355519919195, 360582355065493399, 360582354610996113, 360582353839369611, 360582353558666096, 360582353559390537, 360582353559860389, 360582353232342474]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 39000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 39000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360586911776833133, 360586921136386365⟩, ⟨(-178654056482599127), (-178407206874877625)⟩, true⟩

def words01 : List Nat := [360582353193172021, 360582353137311566, 360582353219185732, 360582353219713275, 360582352704043741, 360582351555565254, 360582350407047573, 360582349357144211, 360582348936791791, 360582349054510584]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 39010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 39000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591548821947627, 360591558186522256⟩, ⟨(-359822305257625512), (-359575259689938366)⟩, true⟩

def words02 : List Nat := [360582349054980527, 360582348844761068, 360582348145895611, 360582348102208997, 360582348058387895, 360582347528897672, 360582347143582835, 360582346430611605, 360582345717572744, 360582345630869316]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 39020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 39000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360541442793670954, 360541452163221877⟩, ⟨1596186733223556707, 1596433973040660557⟩, true⟩

def words03 : List Nat := [360582346173890928, 360582346716995886, 360582346930240393, 360582346930768603, 360582346797537025, 360582346337639721, 360582345901093339, 360582345901621201, 360582345473801322, 360582344426875583]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 39030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 39000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360637514754869731, 360637524129401448⟩, ⟨(-2154928275836635843), (-2154680841544873989)⟩, true⟩

def words04 : List Nat := [360582343379883922, 360582342987423383, 360582343543260593, 360582344148605901, 360582344197729889, 360582344263744898, 360582344983809724, 360582345703992253, 360582346642511508, 360582348056021897]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 39040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 39000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk390A
