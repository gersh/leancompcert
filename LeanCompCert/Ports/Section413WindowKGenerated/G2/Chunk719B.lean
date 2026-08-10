import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk719A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk719B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk719A

def state06 : KState := ⟨⟨360576092786871044, 360576126234506212⟩, ⟨445619760278327101, 447245492347491597⟩, true⟩

def words05 : List Nat := [360582343627237085, 360582343575927491, 360582343524335976, 360582343404208234, 360582343091308945, 360582342602599740, 360582342113708920, 360582341756303656, 360582341515637816, 360582341430342059]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 71950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 71900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360568293876228964, 360568327333588545⟩, ⟨1006787808335794169, 1008414240222227139⟩, true⟩

def words06 : List Nat := [360582341344885730, 360582341125247697, 360582340877432039, 360582340822717175, 360582340767723227, 360582340622534399, 360582340284600835, 360582339783443064, 360582339282098932, 360582338925088090]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 71960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 71900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579011229986350, 360579044696961835⟩, ⟨235443485685615038, 237070609676731080⟩, true⟩

def words07 : List Nat := [360582338731230236, 360582338730317478, 360582338729306004, 360582338581455420, 360582338496589138, 360582338363805350, 360582338251457810, 360582338302985892, 360582338303896197, 360582338259196855]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 71970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 71900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602718543669377, 360602752020303758⟩, ⟨(-1471195367243697971), (-1469567547958828909)⟩, true⟩

def words08 : List Nat := [360582338214285605, 360582338086054456, 360582338264161795, 360582338450162799, 360582338471792279, 360582338472813987, 360582338322511184, 360582338344424468, 360582338523648575, 360582338808263936]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 71980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 71900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360594655305928246, 360594688792299822⟩, ⟨(-890678283824524270), (-889049763511985660)⟩, true⟩

def words09 : List Nat := [360582338973545618, 360582339138923572, 360582339496730262, 360582339985676893, 360582340269344262, 360582340553147591, 360582340725496311, 360582340726518130, 360582340877739959, 360582341050414127]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 71990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 71900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 71900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk719B
