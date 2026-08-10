import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk910A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581373596384025, 360581428075461435⟩, ⟨48074247661537462, 51421987628770526⟩, true⟩

def state01 : KState := ⟨⟨360585195700151107, 360585250191625312⟩, ⟨(-299793350554769366), (-296444482415561222)⟩, true⟩

def words00 : List Nat := [360581993147104690, 360581993204345203, 360581993289255140, 360581993374408015, 360581993375620352, 360581993358060560, 360581993219706550, 360581993079072673, 360581992938041982, 360581992953682475]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 91000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 91000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589464706127172, 360589519210122832⟩, ⟨(-688371090595445517), (-685021082818855551)⟩, true⟩

def words01 : List Nat := [360581992954855331, 360581992915415550, 360581992875729462, 360581992978617029, 360581993043209721, 360581993108016554, 360581993111292853, 360581993112611206, 360581993158491587, 360581993242677750]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 91010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 91000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580535036085849, 360580589552478234⟩, ⟨124403592151888575, 127754728341441929⟩, true⟩

def words02 : List Nat := [360581993323790975, 360581993325105969, 360581993321404114, 360581993257356630, 360581993193104758, 360581993046580973, 360581993003232822, 360581993031455365, 360581993032629249, 360581992987920852]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 91020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 91000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360588824963054929, 360588879491855354⟩, ⟨(-630280323787737969), (-626928058033513783)⟩, true⟩

def words03 : List Nat := [360581992973568053, 360581992971288414, 360581993085411511, 360581993148441473, 360581993149690279, 360581993087168151, 360581993041904095, 360581993121407121, 360581993198116605, 360581993275117473]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 91030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 91000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360578466002257539, 360578520543593652⟩, ⟨312829857828432042, 316183264893669282⟩, true⟩

def words04 : List Nat := [360581993291460117, 360581993313618513, 360581993437362948, 360581993561506116, 360581993637486709, 360581993638801861, 360581993594422938, 360581993456147935, 360581993317639583, 360581993176925818]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 91040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 91000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk910A
