import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk713A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk713B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk713A

def state06 : KState := ⟨⟨362493300316366116, 362493376002579214⟩, ⟨(-584721270710282721), (-581073736935806617)⟩, true⟩

def words05 : List Nat := [371285233013508069, 371285233052355718, 371285233286051347, 371285233288497163, 371285233260789070, 371285233193616629, 371285233125492379, 371285233116596963, 371285233150342425, 371285233267234477]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481228136639802, 362481303844934453⟩, ⟨276791646306419179, 280440755932271637⟩, true⟩

def words06 : List Nat := [371285233382578949, 371285233385027012, 371285233366932752, 371285233458022283, 371285233556680829, 371285233559133890, 371285233456741553, 371285233355597380, 371285233253424769, 371285233237619507]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469721833341156, 362469797563657979⟩, ⟨1098128992370573077, 1101779673831429893⟩, true⟩

def words07 : List Nat := [371285233304012362, 371285233426476826, 371285233529552851, 371285233531999619, 371285233397684904, 371285233317552277, 371285233328940494, 371285233331387452, 371285233188690198, 371285232975171449]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486388297958494, 362486464050171686⟩, ⟨(-91625037902327323), (-87972793365406303)⟩, true⟩

def words08 : List Nat := [371285232760592208, 371285232697441251, 371285232535067733, 371285232429376731, 371285232322905080, 371285232185596778, 371285231884050178, 371285231779791015, 371285231763080043, 371285231782891982]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486740428317188, 362486816202884577⟩, ⟨(-116775513765125941), (-113121673256515179)⟩, true⟩

def words09 : List Nat := [371285231799683356, 371285231817338718, 371285231893351021, 371285231896048123, 371285231926577461, 371285231968883490, 371285232010081818, 371285232012531421, 371285231862604904, 371285231887913407]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk713B
