import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk904A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk904B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk904A

def state06 : KState := ⟨⟨360579552026163905, 360579605835685636⟩, ⟨213170331827752995, 216457322857471087⟩, true⟩

def words05 : List Nat := [360581997909004048, 360581998086548652, 360581998172077095, 360581998319848163, 360581998417986318, 360581998516468641, 360581998649720093, 360581998710844126, 360581998712022672, 360581998686922177]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 90450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 90400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589303191141957, 360589357013005234⟩, ⟨(-668998379696657810), (-665710272189186456)⟩, true⟩

def words06 : List Nat := [360581998661544400, 360581998665835607, 360581998785051428, 360581998904523655, 360581998906386433, 360581998907692421, 360581998787413695, 360581998704160515, 360581998657809859, 360581998740495931]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 90460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 90400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360590029943101484, 360590083777400766⟩, ⟨(-734759540242882752), (-731470307589741638)⟩, true⟩

def words07 : List Nat := [360581998751621161, 360581998762888883, 360581998895950109, 360581999114000615, 360581999217525368, 360581999321232705, 360581999364242024, 360581999365550963, 360581999444474401, 360581999535321327]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 90470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 90400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605744805488149, 360605798652099804⟩, ⟨(-2156677785012316321), (-2153387438273305973)⟩, true⟩

def words08 : List Nat := [360581999747746531, 360582000000780118, 360582000192383855, 360582000384125916, 360582000545010760, 360582000799212756, 360582001125345354, 360582001451720738, 360582001684913940, 360582001949242357]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 90480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 90400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360606175096895961, 360606228955834512⟩, ⟨(-2195663041551930850), (-2192371579289029780)⟩, true⟩

def words09 : List Nat := [360582002254451208, 360582002560034262, 360582002901854804, 360582003121983105, 360582003237323955, 360582003352775373, 360582003438256264, 360582003585417084, 360582003854156727, 360582004123188586]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 90490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 90400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 90400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk904B
