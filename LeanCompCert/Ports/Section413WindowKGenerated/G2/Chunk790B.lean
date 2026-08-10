import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk790A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk790B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk790A

def state06 : KState := ⟨⟨360555199592497000, 360555240267079145⟩, ⟨2129835504324490462, 2132007374229306366⟩, true⟩

def words05 : List Nat := [360582209028143799, 360582208981652740, 360582208935044608, 360582208786817923, 360582208588888985, 360582208318533475, 360582208047846387, 360582207802131455, 360582207560894564, 360582207220965173]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 79050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 79000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583505750525677, 360583546435765817⟩, ⟨(-108156191672926050), (-105983479093342836)⟩, true⟩

def words06 : List Nat := [360582206880787960, 360582206672589248, 360582206574316346, 360582206605709179, 360582206606779160, 360582206483991966, 360582206313967288, 360582206198526752, 360582206082749710, 360582206077365224]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 79060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 79000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360568993298863930, 360569033994876724⟩, ⟨1039490061826576098, 1041663626252467904⟩, true⟩

def words07 : List Nat := [360582206078371800, 360582206016530581, 360582206018580631, 360582206188153122, 360582206315094019, 360582206442215067, 360582206473229780, 360582206474361957, 360582206436666981, 360582206271384722]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 79070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 79000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575294954612147, 360575335661261330⟩, ⟨541053282732971733, 543227688337609695⟩, true⟩

def words08 : List Nat := [360582206105732033, 360582206037004969, 360582205808593306, 360582205472100190, 360582205135428366, 360582204759380479, 360582204508704835, 360582204417847887, 360582204326870617, 360582204136268760]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 79080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 79000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360581207227683764, 360581247945009634⟩, ⟨73395203784047539, 75570453860393303⟩, true⟩

def words09 : List Nat := [360582204090969796, 360582204132861736, 360582204170540185, 360582204171670360, 360582204099890836, 360582203891341905, 360582203682585212, 360582203468814527, 360582203334579613, 360582203323693078]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 79090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 79000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 79000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk790B
