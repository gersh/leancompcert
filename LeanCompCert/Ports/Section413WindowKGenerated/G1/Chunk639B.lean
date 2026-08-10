import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk639A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk639B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk639A

def state06 : KState := ⟨⟨362499926239476338, 362499986524008959⟩, ⟨(-930887993294476654), (-928283655432862910)⟩, true⟩

def words05 : List Nat := [371285470451150512, 371285470651606239, 371285471053449040, 371285471400809448, 371285471821029338, 371285472242049356, 371285472661410925, 371285472789806647, 371285473018226480, 371285473247865171]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 63950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 63900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489553308214668, 362489613612101089⟩, ⟨(-267364872740712086), (-264759296907471402)⟩, true⟩

def words06 : List Nat := [371285473693428398, 371285473813881754, 371285473910936644, 371285474008683503, 371285474117354395, 371285474137641900, 371285474360297809, 371285474583861463, 371285474805771400, 371285474872720628]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 63960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 63900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499878041669591, 362499938365222507⟩, ⟨(-927942713102316234), (-925335879102566378)⟩, true⟩

def words07 : List Nat := [371285475050632438, 371285475229661402, 371285475417642583, 371285475419819540, 371285475344390170, 371285475227860729, 371285475236071423, 371285475242460006, 371285475469992675, 371285475698507349]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 63970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 63900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489620958789875, 362489681301985173⟩, ⟨(-271691426272923954), (-269083335456342896)⟩, true⟩

def words08 : List Nat := [371285475927148198, 371285475929323482, 371285475951780782, 371285476073989143, 371285476254028839, 371285476256217963, 371285476256959166, 371285476175058858, 371285476215316904, 371285476283537949]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 63980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 63900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496046936820263, 362496107299621973⟩, ⟨(-682868551933809890), (-680259206403610852)⟩, true⟩

def words09 : List Nat := [371285476564513883, 371285476846390316, 371285477125101348, 371285477203183467, 371285477354286633, 371285477506436840, 371285477901872647, 371285478079311231, 371285478247042661, 371285478415598230]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 63990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 63900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 63900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk639B
