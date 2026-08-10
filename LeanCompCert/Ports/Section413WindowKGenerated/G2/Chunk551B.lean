import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk551A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk551B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk551A

def state06 : KState := ⟨⟨360619325737183824, 360619344977855396⟩, ⟨(-2072915055073524713), (-2072197983291144837)⟩, true⟩

def words05 : List Nat := [360581774442164791, 360581774878278022, 360581775306219947, 360581775821009848, 360581776055802799, 360581776290647071, 360581776670858267, 360581777254325025, 360581777936016318, 360581778617867522]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 55150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 55100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584366510765315, 360584385758741899⟩, ⟨(-144521189756330657), (-143803714993621279)⟩, true⟩

def words06 : List Nat := [360581779117986861, 360581779290624340, 360581779790991301, 360581780291565160, 360581780469818511, 360581780470585710, 360581780321363528, 360581779879067382, 360581779436640599, 360581779249615844]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 55160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 55100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360575800421870011, 360575819677072519⟩, ⟨328218670226474098, 328936543679329430⟩, true⟩

def words07 : List Nat := [360581779625251446, 360581780001024012, 360581780180859599, 360581780381782095, 360581780496467687, 360581780611359187, 360581780880782964, 360581780938815933, 360581780939505969, 360581780832267868]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 55170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 55100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591950547349839, 360591969809808244⟩, ⟨(-563021984305369163), (-562303710436882045)⟩, true⟩

def words08 : List Nat := [360581780724869994, 360581780729797303, 360581781110015331, 360581781490366562, 360581781597797105, 360581781598565006, 360581781514394218, 360581781357703356, 360581781301848712, 360581781487247739]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 55180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 55100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592789855781398, 360592809125548261⟩, ⟨(-609369020888848701), (-608650343630089229)⟩, true⟩

def words09 : List Nat := [360581781508765400, 360581781530366066, 360581781784018665, 360581782202604421, 360581782367894867, 360581782533292028, 360581782533982431, 360581782649951892, 360581782850329349, 360581783050954865]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 55190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 55100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 55100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk551B
