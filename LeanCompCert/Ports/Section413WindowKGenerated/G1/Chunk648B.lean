import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk648A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk648B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk648A

def state06 : KState := ⟨⟨362472004850468105, 362472066911418683⟩, ⟨870881458259867055, 873600217459926155⟩, true⟩

def words05 : List Nat := [371285537252278060, 371285537061655939, 371285536914731669, 371285536917189191, 371285536844495262, 371285536745812974, 371285536646360268, 371285536546806383, 371285536129899215, 371285535924947205]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 64850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 64800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470382884301577, 362470444964940976⟩, ⟨976142073851692465, 978862110171319411⟩, true⟩

def words06 : List Nat := [371285535718786031, 371285535699968417, 371285535517823088, 371285535336341283, 371285535153988569, 371285535045163991, 371285534843302267, 371285534764985740, 371285534685975185, 371285534561213079]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 64860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 64800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501275565368670, 362501337665995764⟩, ⟨(-1028032795995664048), (-1025311462976528648)⟩, true⟩

def words07 : List Nat := [371285534334895720, 371285534342384108, 371285534523965407, 371285534526174022, 371285534417809691, 371285534271223315, 371285534212082514, 371285534220765950, 371285534465843782, 371285534711926368]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 64870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 64800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362464945755262302, 362465007875852900⟩, ⟨1329190983839178658, 1331913612192456270⟩, true⟩

def words08 : List Nat := [371285534951474378, 371285534953683120, 371285534876683223, 371285534827963826, 371285534785971034, 371285534788179992, 371285534481252560, 371285534167828283, 371285533853509963, 371285533590326509]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 64880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 64800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362451473529484225, 362451535669935312⟩, ⟨2203552264122107105, 2206276181322137253⟩, true⟩

def words09 : List Nat := [371285533275514400, 371285533198858654, 371285533121479986, 371285533010765717, 371285532615095879, 371285532293147083, 371285531970044395, 371285531723887260, 371285531201766850, 371285530680433342]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 64890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 64800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 64800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk648B
