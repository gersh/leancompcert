import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk965A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk965B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk965A

def state06 : KState := ⟨⟨360615804025373391, 360615865648497906⟩, ⟨(-3244712643040675643), (-3240694725117767987)⟩, true⟩

def words05 : List Nat := [360582302838603881, 360582302938292683, 360582303144856687, 360582303301694706, 360582303356593722, 360582303411600173, 360582303573633602, 360582303836808904, 360582304185515841, 360582304534537635]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 96550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 96500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598709377195092, 360598771013663395⟩, ⟨(-1594044970203623521), (-1590025763740208799)⟩, true⟩

def words06 : List Nat := [360582304829810094, 360582305018304641, 360582305282816332, 360582305547741182, 360582305726634539, 360582305832640046, 360582305884543170, 360582305936598218, 360582306004656990, 360582306176768880]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 96560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 96500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569205864006875, 360569267513691046⟩, ⟨1255337532349904342, 1259358015134296498⟩, true⟩

def words07 : List Nat := [360582306436620813, 360582306696760419, 360582306902786869, 360582307022933689, 360582307115914023, 360582307209262585, 360582307227890879, 360582307229292567, 360582307179395700, 360582307045841950]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 96570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 96500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360609196703642865, 360609258366537919⟩, ⟨(-2607198880893654827), (-2603177122134395279)⟩, true⟩

def words08 : List Nat := [360582306911963155, 360582306911281602, 360582307011566409, 360582307112117539, 360582307116316462, 360582307123089398, 360582307236784871, 360582307350904033, 360582307571808349, 360582307852285718]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 96580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 96500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360595959857419319, 360596021533678984⟩, ⟨(-1328592192312521306), (-1324569142602081276)⟩, true⟩

def words09 : List Nat := [360582308052224966, 360582308252304640, 360582308449582994, 360582308723117818, 360582308968933238, 360582309214976968, 360582309407372654, 360582309493081575, 360582309636161954, 360582309779736457]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 96590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 96500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 96500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk965B
