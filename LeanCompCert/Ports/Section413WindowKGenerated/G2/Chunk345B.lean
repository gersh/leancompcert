import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk345A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk345B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk345A

def state06 : KState := ⟨⟨360619550002725235, 360619557272370584⟩, ⟨(-1311335414883175932), (-1311165554474104724)⟩, true⟩

def words05 : List Nat := [360581605650163244, 360581606686386836, 360581608378477667, 360581610606431032, 360581612622042106, 360581614637612276, 360581616231638945, 360581617355531631, 360581618453710768, 360581619551978405]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 34550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 34500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598271786445830, 360598279060449999⟩, ⟨(-575921197232724771), (-575751186160817525)⟩, true⟩

def words06 : List Nat := [360581620513037467, 360581621354170260, 360581621675594769, 360581621997051212, 360581621997438820, 360581622506569924, 360581623327130166, 360581624147730286, 360581624411832039, 360581624894063120]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 34560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 34500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360624182944933356, 360624190223314755⟩, ⟨(-1471944543311434293), (-1471774380897907163)⟩, true⟩

def words07 : List Nat := [360581626024373567, 360581627154754478, 360581627848616668, 360581628007251953, 360581628007679153, 360581627457860560, 360581626944565958, 360581627557800551, 360581628789021302, 360581630020287142]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 34570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 34500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360603536605833838, 360603543888619017⟩, ⟨(-758140102620615809), (-757969787901932989)⟩, true⟩

def words08 : List Nat := [360581630830802091, 360581630831265247, 360581631622446400, 360581632435874075, 360581633037682002, 360581633038145191, 360581632807840414, 360581631898278255, 360581630988680022, 360581631547608294]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 34580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 34500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360556253053342844, 360556260340491324⟩, ⟨877842761141421361, 878013226808135427⟩, true⟩

def words09 : List Nat := [360581633016218549, 360581634484833423, 360581635428777782, 360581636434296410, 360581636607203199, 360581636780223922, 360581637394859272, 360581637395322669, 360581637178266895, 360581636445312369]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 34590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 34500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 34500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk345B
