import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk211A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk211B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk211A

def state06 : KState := ⟨⟨360529723051026494, 360529725662869000⟩, ⟨1075530650074168845, 1075568046932053099⟩, true⟩

def words05 : List Nat := [360580567072182037, 360580567107484769, 360580567107728957, 360580565427950590, 360580563830408354, 360580561673791947, 360580559582406588, 360580559582679073, 360580558312850593, 360580555910833653]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 21150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 21100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360638930579812148, 360638933194231697⟩, ⟨(-1236038532818878034), (-1236001081418203596)⟩, true⟩

def words06 : List Nat := [360580553508985766, 360580551052333737, 360580550623623843, 360580551519603447, 360580551519855259, 360580550330477110, 360580548265940257, 360580547649862173, 360580548636489872, 360580551394533138]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 21160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 21100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360594689197221866, 360594691814234701⟩, ⟨(-299228640770099753), (-299191134456404381)⟩, true⟩

def words07 : List Nat := [360580553043859083, 360580554693059134, 360580557666394508, 360580561768934326, 360580563840281057, 360580565911470945, 360580566580476839, 360580566580749545, 360580565698038654, 360580566365273066]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 21170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 21100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360666694644239666, 360666697263825814⟩, ⟨(-1824658514707835739), (-1824620953878688911)⟩, true⟩

def words08 : List Nat := [360580568441179237, 360580571634957575, 360580573370244525, 360580575105397181, 360580575649427805, 360580577916362820, 360580582398405535, 360580586880077275, 360580589620603134, 360580593684293056]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 21180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 21100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360671270303782811, 360671272925943260⟩, ⟨(-1921405305835476961), (-1921367690444045347)⟩, true⟩

def words09 : List Nat := [360580599962454293, 360580606240102622, 360580614731788690, 360580621006371983, 360580625325119377, 360580629643482857, 360580633308331697, 360580638098774917, 360580642374224386, 360580646649331589]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 21190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 21100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 21100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk211B
