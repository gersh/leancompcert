import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk294A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk294B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk294A

def state06 : KState := ⟨⟨360665055231983759, 360665060443759616⟩, ⟨(-2405845455038695041), (-2405741616243376345)⟩, true⟩

def words05 : List Nat := [360583383310104958, 360583384189634703, 360583386218707461, 360583388830192627, 360583390886874057, 360583392943485941, 360583394422543099, 360583396380531889, 360583399152879385, 360583401925167465]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 29450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 29400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360635933508292669, 360635938723746993⟩, ⟨(-1547958394234383455), (-1547854447053190763)⟩, true⟩

def words06 : List Nat := [360583405083544070, 360583407096244582, 360583408139563057, 360583409182847156, 360583409725055350, 360583410836552972, 360583412768322502, 360583414700035529, 360583415667786499, 360583417450391723]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 29460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 29400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360658104117278372, 360658109336414424⟩, ⟨(-2201511076790697613), (-2201407021090532135)⟩, true⟩

def words07 : List Nat := [360583419563839897, 360583421677257225, 360583424938341007, 360583427054405344, 360583428158254761, 360583429262056071, 360583430337025699, 360583432208886673, 360583434742348046, 360583437275728202]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 29470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 29400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360646660313439541, 360646665536291820⟩, ⟨(-1864372541921457545), (-1864268376648784271)⟩, true⟩

def words08 : List Nat := [360583439160623451, 360583439901025560, 360583441788438447, 360583443675851157, 360583445275293609, 360583446367845462, 360583446887458463, 360583447407079640, 360583448568174916, 360583450712221806]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 29480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 29400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360553532169411417, 360553537395945828⟩, ⟨882319781383298801, 882424055260492741⟩, true⟩

def words09 : List Nat := [360583452239102860, 360583453765947516, 360583454599721190, 360583454600111757, 360583454290224596, 360583453260021603, 360583452229775878, 360583451531173745, 360583451089403961, 360583450075785167]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 29490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 29400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 29400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk294B
