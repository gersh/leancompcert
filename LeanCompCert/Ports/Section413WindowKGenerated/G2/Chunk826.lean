import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk826

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584353542874192, 360584398093110603⟩, ⟨(-170283237216706489), (-167798044537933673)⟩, true⟩

def state01 : KState := ⟨⟨360604623232517963, 360604667793926488⟩, ⟨(-1844668310787595196), (-1842182195236462874)⟩, true⟩

def words00 : List Nat := [360582366836467983, 360582367103824580, 360582367370595227, 360582367637583455, 360582367779800608, 360582367812549775, 360582367840935892, 360582367869652435, 360582368044535423, 360582368315706440]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360606159191403822, 360606203764098935⟩, ⟨(-1971569558646435079), (-1969082510657892373)⟩, true⟩

def words01 : List Nat := [360582368494341250, 360582368673093430, 360582368998116043, 360582369434824166, 360582369757485940, 360582370080329012, 360582370329515309, 360582370472690736, 360582370762116933, 360582371051947571]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589416457232845, 360589461041093214⟩, ⟨(-588299016287566018), (-585811045770088842)⟩, true⟩

def words02 : List Nat := [360582371215768928, 360582371264862738, 360582371265918030, 360582371241513236, 360582371216916981, 360582371175616831, 360582371298598870, 360582371421831136, 360582371471359501, 360582371558383698]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360602311691935522, 360602356286972449⟩, ⟨(-1653909987421750888), (-1651421093328752594)⟩, true⟩

def words03 : List Nat := [360582371709794836, 360582371861557001, 360582372159381803, 360582372350465467, 360582372402093851, 360582372453794333, 360582372554218806, 360582372728677424, 360582372971451107, 360582373214486289]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592791622989682, 360592836229323517⟩, ⟨(-867185725985398285), (-864695898262341039)⟩, true⟩

def words04 : List Nat := [360582373358848037, 360582373506515978, 360582373674499889, 360582373842821401, 360582373974037692, 360582374058605421, 360582374069632888, 360582374080778485, 360582374087636423, 360582374215575803]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360599139574814483, 360599184192307566⟩, ⟨(-1391807928194444774), (-1389317178104242224)⟩, true⟩

def words05 : List Nat := [360582374489460706, 360582374763566058, 360582374964111287, 360582375252365572, 360582375480955740, 360582375709890128, 360582376084765948, 360582376375048986, 360582376579441609, 360582376784000091]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 82650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 82600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360607851850095849, 360607896478786976⟩, ⟨(-2112002780273533336), (-2109511104498096562)⟩, true⟩

def words06 : List Nat := [360582377104792914, 360582377521967472, 360582377926678115, 360582378331589055, 360582378590933223, 360582378704365177, 360582378861333353, 360582379018641321, 360582379226970378, 360582379536878712]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 82660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 82600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599545330614626, 360599589970591831⟩, ⟨(-1425254793446377469), (-1422762184595910075)⟩, true⟩

def words07 : List Nat := [360582379746415017, 360582379956072709, 360582380266236599, 360582380651047377, 360582380996904784, 360582381342954077, 360582381573645246, 360582381702758028, 360582381911847931, 360582382121332680]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 82670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 82600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587916964636233, 360587961615767929⟩, ⟨(-463772495000422777), (-461278963838841863)⟩, true⟩

def words08 : List Nat := [360582382440971014, 360582382614899554, 360582382715272406, 360582382815782868, 360582382838371240, 360582382934445821, 360582383052308936, 360582383170395639, 360582383201627050, 360582383270315113]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 82680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 82600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360600485622591552, 360600530284929237⟩, ⟨(-1503238168353879860), (-1500743710514148512)⟩, true⟩

def words09 : List Nat := [360582383334721344, 360582383399469671, 360582383507650843, 360582383508836347, 360582383503691302, 360582383356817015, 360582383209719559, 360582383222795522, 360582383443186364, 360582383663842260]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 82690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 82600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 82600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk826
