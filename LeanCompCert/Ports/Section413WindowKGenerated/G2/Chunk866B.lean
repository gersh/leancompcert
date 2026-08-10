import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk866A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk866B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk866A

def state06 : KState := ⟨⟨360578496748824652, 360578545968755785⟩, ⟨313217840792592297, 316098310652256893⟩, true⟩

def words05 : List Nat := [360582195185476511, 360582195047613881, 360582194909391756, 360582194767940563, 360582194551024843, 360582194223161861, 360582193895067585, 360582193678088037, 360582193578315807, 360582193537537833]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 86650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 86600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360565961304853285, 360566010536658375⟩, ⟨1399526345434045761, 1402407844348653421⟩, true⟩

def words06 : List Nat := [360582193496568807, 360582193389148345, 360582193148360861, 360582193009152362, 360582192869614472, 360582192696767039, 360582192479758813, 360582192160727509, 360582191841471082, 360582191543285220]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 86660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 86600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561338881793085, 360561388125336269⟩, ⟨1800179764284018883, 1803062280597632931⟩, true⟩

def words07 : List Nat := [360582191357603532, 360582191171519889, 360582190985304604, 360582190724762440, 360582190511391719, 360582190263746542, 360582190015739806, 360582189900938880, 360582189728584427, 360582189489902463]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 86670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 86600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360567696236831536, 360567745492156802⟩, ⟨1249033860399521215, 1251917398042886511⟩, true⟩

def words08 : List Nat := [360582189250953327, 360582188955979876, 360582188727724767, 360582188544832656, 360582188361841942, 360582188065654895, 360582187669858232, 360582187337385029, 360582187004515676, 360582186804857724]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 86680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 86600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360560418732811747, 360560468000009507⟩, ⟨1879944456216955749, 1882829023144130403⟩, true⟩

def words09 : List Nat := [360582186639393258, 360582186353761143, 360582186067896601, 360582185915314496, 360582185829453091, 360582185653332401, 360582185477099003, 360582185208763826, 360582184846793244, 360582184597738967]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 86690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 86600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 86600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk866B
