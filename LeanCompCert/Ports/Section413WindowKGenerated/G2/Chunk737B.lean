import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk737A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk737B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk737A

def state06 : KState := ⟨⟨360589694533988722, 360589729744856449⟩, ⟨(-542058762820354132), (-540304554744847578)⟩, true⟩

def words05 : List Nat := [360582404132357260, 360582404228995725, 360582404468655361, 360582404524891174, 360582404525873969, 360582404393672647, 360582404311551885, 360582404473385038, 360582404573560264, 360582404673955230]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 73750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 73700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598187673250714, 360598222894105271⟩, ⟨(-1168679635295092760), (-1166924690540749118)⟩, true⟩

def words06 : List Nat := [360582404674890991, 360582404659275367, 360582404589015199, 360582404581772645, 360582404574240624, 360582404560191575, 360582404561126231, 360582404488528989, 360582404474981118, 360582404690603343]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 73760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 73700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561672987885645, 360561708218633919⟩, ⟨1525267252003492423, 1527022926665497739⟩, true⟩

def words07 : List Nat := [360582405089324858, 360582405488236380, 360582405745666321, 360582405819637906, 360582405820520984, 360582405783991918, 360582405747162417, 360582405662540731, 360582405474558846, 360582405195140635]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 73770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 73700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584783767716078, 360584819008361895⟩, ⟨(-179932480636561135), (-178176075686012953)⟩, true⟩

def words08 : List Nat := [360582404915469755, 360582404775168513, 360582404859191473, 360582404993523565, 360582404994491126, 360582404971714893, 360582404812599176, 360582404615162735, 360582404417410192, 360582404403929295]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 73780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 73700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575346730353639, 360575381980997829⟩, ⟨516529629597504288, 518286772376642460⟩, true⟩

def words09 : List Nat := [360582404404873792, 360582404344325197, 360582404373450103, 360582404610649714, 360582404801245836, 360582404992010065, 360582405052704873, 360582405053754052, 360582404930944236, 360582404836992093]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 73790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 73700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 73700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk737B
