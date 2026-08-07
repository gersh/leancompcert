import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk104

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360661007992045308, 360661008582755975⟩, ⟨(-828396468689545866), (-828392304690850088)⟩, true⟩

def state01 : KState := ⟨⟨360687895307613600, 360687895899525908⟩, ⟨(-1108543441928758840), (-1108539265426985612)⟩, true⟩

def words00 : List Nat := [360581366081187573, 360581369405075828, 360581378286798889, 360581387166852888, 360581393596529956, 360581400812019360, 360581403328850716, 360581405845212240, 360581407977631532, 360581418206179738]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 10400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 10400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360454990422158659, 360454991015259655⟩, ⟨1317689093277022978, 1317693282159030666⟩, true⟩

def words01 : List Nat := [360581432932568024, 360581447656152018, 360581456274939940, 360581460555369993, 360581462403685262, 360581464251681239, 360581467297331092, 360581467297457379, 360581461240885757, 360581449103758603]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 10410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 10400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360684792974486602, 360684793568782164⟩, ⟨(-1078647812161105664), (-1078643610825785272)⟩, true⟩

def words02 : List Nat := [360581436968932847, 360581427613339161, 360581423035958395, 360581418093970713, 360581413152921347, 360581400329869060, 360581385120458746, 360581379077417596, 360581376156297822, 360581386070860030]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 10420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 10400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360614568671442695, 360614569266942986⟩, ⟨(-345467018868809412), (-345462804962241412)⟩, true⟩

def words03 : List Nat := [360581389813443557, 360581393555322168, 360581406452860951, 360581425763201484, 360581442660671156, 360581459554923439, 360581468954113360, 360581475789832133, 360581478959808995, 360581482129220331]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 10430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 10400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360673537011029166, 360673537607720857⟩, ⟨(-961667968614483142), (-961663742263808210)⟩, true⟩

def words04 : List Nat := [360581491061710864, 360581496548338348, 360581496563768640, 360581496579211895, 360581496579317887, 360581496393795882, 360581503503220027, 360581510611307421, 360581512369094566, 360581521174627009]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 10440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 10400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360836376215744168, 360836376813632741⟩, ⟨(-2664860732927640395), (-2664856494063584241)⟩, true⟩

def words05 : List Nat := [360581529634739026, 360581538093268019, 360581555666910745, 360581564202103912, 360581564202220984, 360581563366776595, 360581570806754019, 360581586059592315, 360581610418275694, 360581634772330420]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 10450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 10400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360625196951764362, 360625197550860127⟩, ⟨(-455518355845868791), (-455514104348450111)⟩, true⟩

def words06 : List Nat := [360581652212935214, 360581660625425200, 360581678141064998, 360581695653394110, 360581704499787347, 360581704499914300, 360581704323236423, 360581699537139949, 360581694751934025, 360581695105597168]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 10460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 10400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360524609734064992, 360524610334358882⟩, ⟨598258438802901473, 598262702850713971⟩, true⟩

def words07 : List Nat := [360581704157881472, 360581713208464447, 360581717626724287, 360581717626851309, 360581713030997914, 360581705784539950, 360581700373680044, 360581701917550763, 360581701917665884, 360581696470127080]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 10470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 10400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360716899957980107, 360716900559472950⟩, ⟨(-1417958424679803608), (-1417954148060944934)⟩, true⟩

def words08 : List Nat := [360581691023599416, 360581695185500549, 360581700709782377, 360581706233033956, 360581706233152134, 360581703907110665, 360581710318389298, 360581718052955703, 360581728571919101, 360581741456617079]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 10480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 10400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360703094207044393, 360703094809750482⟩, ⟨(-1273394430357439001), (-1273390141005676991)⟩, true⟩

def words09 : List Nat := [360581748493190164, 360581755528435461, 360581762229988927, 360581775970592606, 360581787348853471, 360581798724967143, 360581805491848107, 360581808006851611, 360581819558078814, 360581831107150189]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 10490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 10400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 10400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk104
