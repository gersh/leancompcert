import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk525

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360568323587522096, 360568340947491854⟩, ⟨719178470071085627, 719794281602859639⟩, true⟩

def state01 : KState := ⟨⟨360544729207123180, 360544746573936403⟩, ⟨1957992264883036952, 1958608435731709784⟩, true⟩

def words00 : List Nat := [360582051155087714, 360582051155814955, 360582050895500149, 360582050299729970, 360582049703863860, 360582049017423189, 360582048510899321, 360582047849704138, 360582047188455708, 360582046296574600]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 52500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 52500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360604461790877893, 360604479164557954⟩, ⟨(-1178872292626643412), (-1178255761166644706)⟩, true⟩

def words01 : List Nat := [360582045586840693, 360582045239242760, 360582044891446366, 360582044666150461, 360582044660211872, 360582044347663800, 360582044083547236, 360582044315611422, 360582044743367860, 360582045171275903]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 52510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 52500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360577718061597999, 360577735442213832⟩, ⟨225609657576814358, 226226553337496630⟩, true⟩

def words02 : List Nat := [360582045272027284, 360582045272754923, 360582045011829479, 360582044998382774, 360582044984741281, 360582044725066161, 360582044103747318, 360582043301448031, 360582042499027086, 360582042058496671]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 52520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 52500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360536543796292982, 360536561183758526⟩, ⟨2388771107882408063, 2389388363492230943⟩, true⟩

def words03 : List Nat := [360582042178476718, 360582042380571860, 360582042381229298, 360582042352542080, 360582041962273648, 360582041286985242, 360582040611503811, 360582040222618481, 360582039558373217, 360582038693531885]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 52530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 52500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574464240406393, 360574481634755787⟩, ⟨396386544346605881, 397004161666633013⟩, true⟩

def words04 : List Nat := [360582037828558135, 360582037325291321, 360582037236362372, 360582037373043012, 360582037373714848, 360582037223189514, 360582037113977954, 360582036887232503, 360582036660291729, 360582036423750395]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 52540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 52500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360577301570050917, 360577318971338780⟩, ⟨247291201714719746, 247909183685962544⟩, true⟩

def words05 : List Nat := [360582036280644035, 360582035955947217, 360582035667015616, 360582035922340398, 360582035982961528, 360582036043710893, 360582036044359663, 360582035924218847, 360582035749428766, 360582035660526109]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 52550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 52500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591812123471922, 360591829531623817⟩, ⟨(-515491738776006582), (-514873395996636088)⟩, true⟩

def words06 : List Nat := [360582035842840390, 360582035908916568, 360582035909576620, 360582035696896528, 360582035484103816, 360582035181050040, 360582035299725544, 360582035540053293, 360582035540713371, 360582035664358659]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 52560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 52500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360612281668661793, 360612299083688360⟩, ⟨(-1591693543319733050), (-1591074839105746714)⟩, true⟩

def words07 : List Nat := [360582036212326529, 360582036760490935, 360582037468282459, 360582037930758537, 360582038086379168, 360582038242050646, 360582038242650806, 360582038430005722, 360582039006111068, 360582039582364579]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 52570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 52500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594145602549768, 360594163024505943⟩, ⟨(-638152145666402790), (-637533077058121376)⟩, true⟩

def words08 : List Nat := [360582039906439472, 360582039988801173, 360582040431964139, 360582040875337755, 360582041115575354, 360582041116303907, 360582040995876194, 360582040694254947, 360582040392505918, 360582040549613697]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 52580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 52500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360562853874824081, 360562871303653543⟩, ⟨1007530056144312408, 1008149486252304946⟩, true⟩

def words09 : List Nat := [360582040595981769, 360582040642474960, 360582040643124290, 360582040476003113, 360582039948135969, 360582039265426472, 360582038582521156, 360582038175256775, 360582038007327159, 360582037643696363]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 52590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 52500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 52500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk525
