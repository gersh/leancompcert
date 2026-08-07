import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk803

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497017433184205, 362497114150950819⟩, ⟨(-964017312756746701), (-958772976319993219)⟩, true⟩

def state01 : KState := ⟨⟨362487426669992157, 362487523412791150⟩, ⟨(-193880856505436746), (-188634509839953746)⟩, true⟩

def words00 : List Nat := [371285174553233128, 371285174556009367, 371285174563163330, 371285174639351329, 371285174761658321, 371285174764434635, 371285174680281752, 371285174596564131, 371285174579965683, 371285174612379750]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 80300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 80300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480566373861842, 362480663141722851⟩, ⟨357101513765915795, 362349873288441701⟩, true⟩

def words01 : List Nat := [371285174651876250, 371285174692480298, 371285174725158716, 371285174727948602, 371285174612151398, 371285174545338448, 371285174561856188, 371285174564681333, 371285174522833077, 371285174469826542]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 80310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 80300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488197281567678, 362488294074265934⟩, ⟨(-255818654051058814), (-250568299474144056)⟩, true⟩

def words02 : List Nat := [371285174488337219, 371285174509330561, 371285174661224600, 371285174814220683, 371285174911638002, 371285174914415020, 371285174805004370, 371285174764816287, 371285174834497032, 371285174876204487]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 80320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 80300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362476649800192312, 362476746618201406⟩, ⟨671887379930696699, 677139767855470639⟩, true⟩

def words03 : List Nat := [371285174917151528, 371285174959069253, 371285175059009889, 371285175083094074, 371285175153644370, 371285175225293701, 371285175287545793, 371285175290323268, 371285175145972227, 371285175044487882]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 80330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 80300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481049495679339, 362481146338409052⟩, ⟨318424403013351399, 323678777120920987⟩, true⟩

def words04 : List Nat := [371285174991381468, 371285174994166903, 371285174893818258, 371285174798461433, 371285174701996787, 371285174654306144, 371285174596215651, 371285174646618726, 371285174696165972, 371285174699045281]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 80340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 80300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362482951683152811, 362483048551074255⟩, ⟨165575230283108519, 170831628663926421⟩, true⟩

def words05 : List Nat := [371285174715021865, 371285174782646597, 371285174886375853, 371285174889153905, 371285174786753701, 371285174639558592, 371285174491261479, 371285174483868743, 371285174403451320, 371285174380201482]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 80350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 80300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486260447682696, 362486357340685119⟩, ⟨(-100379570166939700), (-95121156152177822)⟩, true⟩

def words06 : List Nat := [371285174355844341, 371285174331664550, 371285174139942334, 371285174104371289, 371285174076215497, 371285174079026443, 371285173997571073, 371285173880515813, 371285173796900547, 371285173814834350]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 80360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 80300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480290970833210, 362480387888811620⟩, ⟨379490698917956174, 384751120382267910⟩, true⟩

def words07 : List Nat := [371285173975017242, 371285174136302692, 371285174296174051, 371285174328295267, 371285174406429249, 371285174485967822, 371285174643446061, 371285174646225123, 371285174597672245, 371285174541217471]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 80370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 80300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483540584037219, 362483637526934376⟩, ⟨118285897311722529, 123548321866609849⟩, true⟩

def words08 : List Nat := [371285174488067514, 371285174491130274, 371285174476087890, 371285174535124969, 371285174554313678, 371285174557093022, 371285174369820918, 371285174338705930, 371285174385878926, 371285174388756327]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 80380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 80300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476758339221028, 362476855307446218⟩, ⟨663569273268512086, 668833734070375400⟩, true⟩

def words09 : List Nat := [371285174371716755, 371285174349893580, 371285174399897395, 371285174402960636, 371285174403221215, 371285174408868758, 371285174413168051, 371285174415948294, 371285174234965967, 371285174134984407]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 80390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 80300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 80300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk803
