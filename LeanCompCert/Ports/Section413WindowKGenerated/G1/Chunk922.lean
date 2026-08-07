import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk922

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473913187738964, 362474042061160023⟩, ⟨1011773049787446733, 1019795559041949185⟩, true⟩

def state01 : KState := ⟨⟨362478254202483236, 362478383104770719⟩, ⟨611577552798538900, 619602723681396602⟩, true⟩

def words00 : List Nat := [371285102632743600, 371285102624345941, 371285102643323771, 371285102714028516, 371285102767731735, 371285102770955457, 371285102667616153, 371285102621383124, 371285102575716591, 371285102579054218]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 92200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 92200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480218741355757, 362480347672984996⟩, ⟨430395308317594861, 438423184953406599⟩, true⟩

def words01 : List Nat := [371285102508635128, 371285102416341566, 371285102322781819, 371285102273436615, 371285102176838809, 371285102117570508, 371285102057185997, 371285101988368725, 371285101821473724, 371285101773884513]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 92210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 92200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480345121220774, 362480474081563267⟩, ⟨418760899890046564, 426791424608707336⟩, true⟩

def words02 : List Nat := [371285101790491995, 371285101793731801, 371285101749360880, 371285101706497120, 371285101662378467, 371285101607405107, 371285101518356454, 371285101534965117, 371285101546772574, 371285101550115894]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 92220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 92200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495230860364394, 362495359849931842⟩, ⟨(-954204506450920131), (-946171286173282915)⟩, true⟩

def words03 : List Nat := [371285101556484219, 371285101614835108, 371285101788869097, 371285101819908104, 371285101825824597, 371285101832686374, 371285101955754932, 371285102021576423, 371285102135009428, 371285102249882263]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 92230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 92200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494983555375577, 362495112574063169⟩, ⟨(-931422193581195220), (-923386287113921404)⟩, true⟩

def words04 : List Nat := [371285102351933399, 371285102355167395, 371285102433536810, 371285102534190701, 371285102660201288, 371285102721755591, 371285102772749016, 371285102824876716, 371285102962894016, 371285103075118834]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 92240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 92200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362483553048429894, 362483682096161469⟩, ⟨123159192018857159, 131197777942248633⟩, true⟩

def words05 : List Nat := [371285103303268587, 371285103532697642, 371285103737092982, 371285103795783789, 371285103889519678, 371285103984900055, 371285104138564391, 371285104149459005, 371285104151902148, 371285104140145235]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 92250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 92200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485368675696811, 362485497752271602⟩, ⟨(-44339682487274488), (-36298435338368970)⟩, true⟩

def words06 : List Nat := [371285104170360355, 371285104173915641, 371285104252781932, 371285104348151800, 371285104423913279, 371285104427139398, 371285104346104005, 371285104311874993, 371285104355246303, 371285104362849808]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 92260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 92200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491553311513771, 362491682417518450⟩, ⟨(-615008989259693060), (-606965026469313462)⟩, true⟩

def words07 : List Nat := [371285104369279972, 371285104376843362, 371285104484319725, 371285104561569015, 371285104673063034, 371285104785774395, 371285104897812474, 371285104912329057, 371285104985809296, 371285105061112806]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 92270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 92200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480551821997872, 362480680956787380⟩, ⟨400251023310266675, 408297642513626907⟩, true⟩

def words08 : List Nat := [371285105183549162, 371285105186775717, 371285105152933116, 371285105118173225, 371285105082206803, 371285105083544734, 371285105025542970, 371285105027322974, 371285105027904041, 371285105029195156]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 92280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 92200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489999450840039, 362490128614716022⟩, ⟨(-471729164044972227), (-463679860301870739)⟩, true⟩

def words09 : List Nat := [371285105024304653, 371285105068987521, 371285105164296219, 371285105167523219, 371285105106773471, 371285105021596994, 371285104963708505, 371285104967264963, 371285104993977250, 371285105052021124]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 92290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 92200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 92200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk922
