import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk217

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360548685253102320, 360548688006111291⟩, ⟨681117775273396217, 681158197498605257⟩, true⟩

def state01 : KState := ⟨⟨360577940764566533, 360577943520217616⟩, ⟨46250218409900804, 46290697982378558⟩, true⟩

def words00 : List Nat := [360580077007858836, 360580078744505965, 360580080775608620, 360580082806576082, 360580083011155796, 360580083011435949, 360580081105349556, 360580079093682478, 360580077082116620, 360580075749512060]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 21700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 21700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569971509511606, 360569974267829640⟩, ⟨219441869440932672, 219482406925914800⟩, true⟩

def words01 : List Nat := [360580075651552025, 360580074489795601, 360580074279373917, 360580077213956857, 360580079069525901, 360580080924969731, 360580081424738480, 360580081425018813, 360580079815966926, 360580079351021441]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 21710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 21700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360527272242662521, 360527275003624635⟩, ⟨1146656842467418286, 1146697437394861562⟩, true⟩

def words02 : List Nat := [360580078886030564, 360580077645126143, 360580074295943690, 360580069558083213, 360580064820615074, 360580058587958122, 360580053935116948, 360580051393606560, 360580048852294705, 360580045249247961]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 21720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 21700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360610193501102129, 360610196264711069⟩, ⟨(-655854461322654102), (-655813808866529848)⟩, true⟩

def words03 : List Nat := [360580042821135629, 360580041628694067, 360580040739199826, 360580040739480387, 360580038935901482, 360580035043653221, 360580031151705871, 360580029368769246, 360580030035862090, 360580031423679538]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 21730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 21700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360546470477269917, 360546473243553934⟩, ⟨729726163152605565, 729766873778209267⟩, true⟩

def words04 : List Nat := [360580031751068684, 360580032149852087, 360580033228223999, 360580034306580745, 360580034849945990, 360580034850226697, 360580034003210134, 360580031567635527, 360580029132236303, 360580025743497760]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 21740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 21700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360557653461651879, 360557656230579103⟩, ⟨486495717185125288, 486536485313734320⟩, true⟩

def words05 : List Nat := [360580024764767098, 360580025328610927, 360580025328863297, 360580024837168068, 360580023023834389, 360580020127093599, 360580017230531841, 360580016471101723, 360580016471351879, 360580015444058595]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 21750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 21700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360616202832918095, 360616205604499767⟩, ⟨(-787855765389206342), (-787814939486596378)⟩, true⟩

def words06 : List Nat := [360580014780149024, 360580016538144329, 360580018228693276, 360580019919136638, 360580019919395508, 360580019795674139, 360580017572034440, 360580017451789252, 360580017504089910, 360580019166601343]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 21760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 21700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360565050660214730, 360565053434474712⟩, ⟨326099697436552070, 326140581658798180⟩, true⟩

def words07 : List Nat := [360580019330818703, 360580019495049291, 360580021761176859, 360580025344428090, 360580027626847272, 360580029909101261, 360580030222066824, 360580030222347991, 360580028436751105, 360580027749518734]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 21770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 21700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360557478583973015, 360557481360878106⟩, ⟨490869655626894986, 490910597473297324⟩, true⟩

def words08 : List Nat := [360580027320614403, 360580027320895617, 360580025481362137, 360580022379262670, 360580019277397457, 360580015643072599, 360580013067059603, 360580012590287079, 360580012113528836, 360580010530105885]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 21780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 21700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586361793817030, 360586364573381337⟩, ⟨(-139110488948777839), (-139069489144890513)⟩, true⟩

def words09 : List Nat := [360580009496463969, 360580007374859624, 360580005253368805, 360580002875754308, 360579999848720754, 360579995014539276, 360579990180747736, 360579986750466425, 360579985238725356, 360579985531633487]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 21790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 21700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 21700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk217
