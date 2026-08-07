import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk005

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨363844523746704509, 363844523748950864⟩, ⟨(-710441261792656338), (-710441261025630346)⟩, true⟩

def state01 : KState := ⟨⟨363660727769710560, 363660727772054369⟩, ⟨(-625880800916888752), (-625880800100632794)⟩, true⟩

def words00 : List Nat := [371229170063925313, 371229170063936052, 371228163629027638, 371229594021090085, 371231894088780244, 371231894088791143, 371231372606983108, 371230819773714969, 371233510516942711, 371235912116280137]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361652903630021518, 361652903632465558⟩, ⟨411157662404403054, 411157663272289712⟩, true⟩

def words01 : List Nat := [371239713967123090, 371243500995939812, 371247163191808554, 371247163191819625, 371245919303622845, 371245628121949400, 371246603907816380, 371246603907827774, 371245114929702021, 371243591446450731]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362951475642261857, 362951475644807207⟩, ⟨(-261251409171333313), (-261251408250243159)⟩, true⟩

def words02 : List Nat := [371244139329105519, 371244715430261056, 371248853341827662, 371252975489925999, 371256185737444986, 371256185737456322, 371255139076414484, 371255560016785269, 371258548459417622, 371259476759213529]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361154317889353968, 361154317892004456⟩, ⟨706910360126685424, 706910361104039370⟩, true⟩

def words03 : List Nat := [371260143158718096, 371260807057665508, 371263163655508442, 371263846216713132, 371265475154584787, 371267098025653156, 371268688295875165, 371268688295886815, 371265839897749136, 371263411153308233]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361564547201329979, 361564547204085609⟩, ⟨484317780565350922, 484317781600035748⟩, true⟩

def words04 : List Nat := [371261877489520460, 371261877489532162, 371258384240801934, 371254918157396134, 371251464793558004, 371249018534618307, 371245678288196520, 371245555234771260, 371245432629624389, 371245124988812947]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362452905905184865, 362452905908049274⟩, ⟨(-10702754043963812), (-10702752948889240)⟩, true⟩

def words05 : List Nat := [371243742109171970, 371243956595801032, 371245437398663283, 371245437398675268, 371242742354803288, 371239293835097072, 371235857697862790, 371235515248807308, 371233793849198165, 371233827917053037]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360628093204890754, 360628093207865517⟩, ⟨1012613812146328042, 1012613813303779982⟩, true⟩

def words06 : List Nat := [371233827917062254, 371232921481946548, 371227955161940939, 371226023458836483, 371224098593613532, 371223156852431723, 371218211116536946, 371212674722906958, 371207157789355161, 371204608669801974]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361161979540574090, 361161979543661904⟩, ⟨712985251293296136, 712985252515768494⟩, true⟩

def words07 : List Nat := [371201497434325524, 371201331411464529, 371201165968085903, 371201029276066348, 371198639668382128, 371196646922440080, 371195564401897545, 371195564401910182, 371193387579081029, 371191264461792540]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361118156017648354, 361118156020850680⟩, ⟨739997141000925898, 739997142290406978⟩, true⟩

def words08 : List Nat := [371189148652992173, 371188207963494895, 371185839301136235, 371184777564114172, 371183719456958443, 371182394850311479, 371177337142065552, 371175065012654639, 371172800598447529, 371172388465410692]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362326835476725994, 362326835480046804⟩, ⟨21073918244351609, 21073919604345229⟩, true⟩

def words09 : List Nat := [371170266244702038, 371168235372448367, 371166905699063339, 371166905699077722, 371166596736177837, 371165948438909494, 371165302313487214, 371164756984594686, 371162017315764172, 371161958679387380]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk005
