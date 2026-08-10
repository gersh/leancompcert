import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk715A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk715B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk715A

def state06 : KState := ⟨⟨360577068230447427, 360577101292605892⟩, ⟨372221497751481404, 373819567964092624⟩, true⟩

def words05 : List Nat := [360582324757434721, 360582324958298494, 360582324994118011, 360582325102249367, 360582325103104790, 360582325084371798, 360582325199749089, 360582325225688159, 360582325226601216, 360582325154651226]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 71550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 71500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360615393130660131, 360615426202416523⟩, ⟨(-2370567800870768860), (-2368969043782708966)⟩, true⟩

def words06 : List Nat := [360582325082487680, 360582325027458197, 360582325244306888, 360582325461343826, 360582325509091851, 360582325528526583, 360582325678208025, 360582325828213137, 360582326172806282, 360582326636338326]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 71560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 71500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606506323761705, 360606539405184038⟩, ⟨(-1734502658791821594), (-1732903209864571768)⟩, true⟩

def words07 : List Nat := [360582327002216792, 360582327368196516, 360582327820199116, 360582328386059058, 360582328814629032, 360582329243338139, 360582329522462506, 360582329743808749, 360582330082848663, 360582330422215589]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 71570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 71500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360609991906230817, 360610024997226515⟩, ⟨(-1983990761912387549), (-1982390627675860797)⟩, true⟩

def words08 : List Nat := [360582330893966075, 360582331371129519, 360582331732735145, 360582332094441249, 360582332376385009, 360582332796773247, 360582333283454859, 360582333770321882, 360582334108793276, 360582334496637393]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 71580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 71500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360618637910851259, 360618671011431406⟩, ⟨(-2603008202643414513), (-2601407382208592925)⟩, true⟩

def words09 : List Nat := [360582334942105879, 360582335387858332, 360582336028071450, 360582336473812605, 360582336732613257, 360582336991493549, 360582337444911646, 360582337996768352, 360582338505040694, 360582339013523436]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 71590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 71500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 71500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk715B
