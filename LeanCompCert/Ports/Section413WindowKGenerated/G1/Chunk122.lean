import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk122

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362562203464929869, 362562205372434479⟩, ⟨(-947582177624595696), (-947566429101990242)⟩, true⟩

def state01 : KState := ⟨⟨362509969360877912, 362509971271659865⟩, ⟨(-310372610459574414), (-310356821936879712)⟩, true⟩

def words00 : List Nat := [371284547603707166, 371284547604069638, 371284546934866730, 371284549940127132, 371284555026391101, 371284555026754612, 371284553364112285, 371284551635018621, 371284553022109029, 371284555104111190]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 12200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 12200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362459844551468171, 362459846465511138⟩, ⟨302273856460259563, 302289684816798995⟩, true⟩

def words01 : List Nat := [371284563857326407, 371284572609251714, 371284580485053909, 371284581020449317, 371284581667698066, 371284582315017651, 371284587830859885, 371284587831223222, 371284585779682135, 371284583755594346]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 12210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 12200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362454512330533447, 362454514247832194⟩, ⟨367675395859521074, 367691264018531400⟩, true⟩

def words02 : List Nat := [371284582421185286, 371284582421595677, 371284583129652711, 371284585571346518, 371284586798210208, 371284586798573580, 371284579142399830, 371284578141617652, 371284578946067625, 371284578946443685]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 12220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 12200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484822671003069, 362484824591623682⟩, ⟨(-3186024802658913), (-3170116000910947)⟩, true⟩

def words03 : List Nat := [371284576488645031, 371284573803197626, 371284572762164621, 371284572762564808, 371284571427988376, 371284571796232300, 371284572193070000, 371284572193434114, 371284565594758777, 371284565616376488]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 12230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 12200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362447262072930398, 362447263996796299⟩, ⟨456782026122732652, 456797974663726640⟩, true⟩

def words04 : List Nat := [371284572276863499, 371284572277227371, 371284570077337433, 371284565869555806, 371284561662326487, 371284559046009000, 371284553990357705, 371284553898695528, 371284553806925589, 371284553627381094]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 12240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 12200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362523759390177374, 362523761317332350⟩, ⟨(-480272771759637399), (-480256782910552001)⟩, true⟩

def words05 : List Nat := [371284554167800794, 371284557751621770, 371284567960879638, 371284572229792236, 371284575944058710, 371284579657836258, 371284584183546894, 371284585463597126, 371284588659266981, 371284591854571519]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 12250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 12200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362430068542347140, 362430070472788602⟩, ⟨668538115572358270, 668554144730810166⟩, true⟩

def words06 : List Nat := [371284594183993807, 371284594184358449, 371284587796286824, 371284587912292633, 371284587914094133, 371284587914458863, 371284579088097401, 371284569640571849, 371284560194442304, 371284557363149712]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 12260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 12200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362437913010614145, 362437914944351841⟩, ⟨572358851045524192, 572374920665417344⟩, true⟩

def words07 : List Nat := [371284552923104647, 371284551272221860, 371284549621479226, 371284548003147746, 371284541103615416, 371284536169129842, 371284532905330866, 371284532905702035, 371284529075437242, 371284525279910915]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 12270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 12200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362505197473046924, 362505199410052337⟩, ⟨(-253910095455226198), (-253893985691190610)⟩, true⟩

def words08 : List Nat := [371284524290124599, 371284524443553924, 371284530121184116, 371284535798034512, 371284540455192967, 371284540455558268, 371284536312706852, 371284535621043347, 371284540826623803, 371284542507791237]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 12280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 12200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362526542927084876, 362526544867421646⟩, ⟨(-516311946379755063), (-516295795656574279)⟩, true⟩

def words09 : List Nat := [371284543268745697, 371284544029701611, 371284549641189763, 371284552012717433, 371284556425066842, 371284560836841349, 371284565286934796, 371284566185879813, 371284569599033743, 371284573011828071]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 12290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 12200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 12200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk122
