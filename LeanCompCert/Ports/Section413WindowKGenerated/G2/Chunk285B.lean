import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk285A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk285B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk285A

def state06 : KState := ⟨⟨360624631282605825, 360624636167796723⟩, ⟨(-1210063202170470860), (-1209968838436446008)⟩, true⟩

def words05 : List Nat := [360582258210414580, 360582259834287024, 360582261428490360, 360582263638382070, 360582265537929349, 360582267437407622, 360582268565573257, 360582268827915882, 360582270311671144, 360582271795455543]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 28550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 28500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360556573374301285, 360556578263040897⟩, ⟨733970754371003289, 734065219474114731⟩, true⟩

def words06 : List Nat := [360582273651138064, 360582274289212361, 360582274316577586, 360582274343982203, 360582274344298124, 360582274035500157, 360582274035812670, 360582273535631954, 360582273035445261, 360582271830400860]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 28560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 28500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360675532776888518, 360675537669188352⟩, ⟨(-2665291229621813301), (-2665196662785512447)⟩, true⟩

def words07 : List Nat := [360582271252822645, 360582271574620526, 360582273116830943, 360582275234124392, 360582276292459321, 360582277350746961, 360582278454980842, 360582280498445474, 360582283761772666, 360582287024956677]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 28570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 28500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608587554123291, 360608592450019770⟩, ⟨(-751815678747004833), (-751721009100502153)⟩, true⟩

def words08 : List Nat := [360582289332784152, 360582290936639239, 360582293427658609, 360582295918617819, 360582298099615053, 360582299064896995, 360582299251035024, 360582299437206097, 360582299437513855, 360582300224875477]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 28580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 28500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589855369129298, 360589860268580156⟩, ⟨(-215994156497538028), (-215899385213747242)⟩, true⟩

def words09 : List Nat := [360582302363961174, 360582304502969405, 360582305999281267, 360582307500681764, 360582307994262729, 360582308487902764, 360582310200128615, 360582311074337464, 360582311338631722, 360582311602966585]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 28590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 28500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 28500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk285B
