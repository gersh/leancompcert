import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk657A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk657B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk657A

def state06 : KState := ⟨⟨360603650672229308, 360603678405166048⟩, ⟨(-1366530971292898675), (-1365299039899538655)⟩, true⟩

def words05 : List Nat := [360582915124956298, 360582915106243583, 360582915222084889, 360582915503678812, 360582915727006222, 360582915950480460, 360582916024427681, 360582916240917810, 360582916557395217, 360582916874168960]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 65750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 65700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595250251995711, 360595277993651701⟩, ⟨(-814056989499743371), (-812824484683547873)⟩, true⟩

def words06 : List Nat := [360582917421522992, 360582917797339618, 360582918056775400, 360582918316297036, 360582918416938287, 360582918656435292, 360582918964126793, 360582919271982826, 360582919402382245, 360582919591245116]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 65760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 65700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602436854348876, 360602464604775813⟩, ⟨(-1286783898716939850), (-1285550816995440078)⟩, true⟩

def words07 : List Nat := [360582919954124338, 360582920317293681, 360582920673247233, 360582920798902498, 360582920799758492, 360582920728446785, 360582920815520458, 360582921119300040, 360582921417166535, 360582921715233310]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 65770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 65700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360617882896289432, 360617910655543397⟩, ⟨(-2303061402810249325), (-2301827740404142527)⟩, true⟩

def words08 : List Nat := [360582921897018023, 360582921941547197, 360582922166294396, 360582922391306654, 360582922502722034, 360582922694378390, 360582922770250780, 360582922846221992, 360582923152718685, 360582923685586958]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 65780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 65700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580547604411517, 360580575372410125⟩, ⟨153440058917683877, 154674296677949349⟩, true⟩

def words09 : List Nat := [360582924253917899, 360582924822404037, 360582925201062526, 360582925418970105, 360582925578793931, 360582925738858554, 360582925998863146, 360582926079524014, 360582926080358861, 360582926045611918]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 65790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 65700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 65700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk657B
