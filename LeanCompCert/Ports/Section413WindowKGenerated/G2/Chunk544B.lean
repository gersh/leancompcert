import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk544A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk544B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk544A

def state06 : KState := ⟨⟨360562748290353017, 360562767026423258⟩, ⟨1034271618036410191, 1034961032252561153⟩, true⟩

def words05 : List Nat := [360581770287592725, 360581770867661952, 360581771185953796, 360581771363411932, 360581771456077782, 360581771548940533, 360581771609817888, 360581771610574539, 360581771433203940, 360581771085039721]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 54450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 54400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585521991865103, 360585540735075433⟩, ⟨(-206125518347443034), (-205435715247065624)⟩, true⟩

def words06 : List Nat := [360581770736707581, 360581770439530512, 360581770530420980, 360581770709338222, 360581770710035938, 360581770601968261, 360581770235806207, 360581769777285579, 360581769318549981, 360581769265573367]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 54460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 54400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360570451490671774, 360570470241083689⟩, ⟨614826442132593913, 615516637539817371⟩, true⟩

def words07 : List Nat := [360581769266247682, 360581769129612463, 360581768992833959, 360581768989247834, 360581769029733645, 360581769070340667, 360581769071021214, 360581768942044592, 360581768476927268, 360581768270407108]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 54470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 54400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360529277339100251, 360529296096651420⟩, ⟨2858095783791125926, 2858786368180299514⟩, true⟩

def words08 : List Nat := [360581768063654444, 360581767765576576, 360581767131458906, 360581766214897473, 360581765298247824, 360581764181967824, 360581763238294770, 360581762402701471, 360581761567043227, 360581760518897343]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 54480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 54400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360584158833799346, 360584177598495674⟩, ⟨(-132738413369221548), (-132047439605274134)⟩, true⟩

def words09 : List Nat := [360581759556701177, 360581758776674913, 360581757996453640, 360581757552472542, 360581757057102110, 360581756244523699, 360581755431826616, 360581754955406514, 360581754708910867, 360581754754151437]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 54490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 54400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 54400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk544B
