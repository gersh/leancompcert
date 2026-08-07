import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk557

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483182973495309, 362483228194313213⟩, ⟨93693555222803463, 95395090053980603⟩, true⟩

def state01 : KState := ⟨⟨362469033195113664, 362469078432862283⟩, ⟨881869474110232703, 883571952068529733⟩, true⟩

def words00 : List Nat := [371284940823690247, 371284940792505167, 371284940331544584, 371284940148120796, 371284939963752319, 371284939837849395, 371284939506109154, 371284939171911253, 371284938836980735, 371284938636633034]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 55700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 55700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362460930714307835, 362460975968972717⟩, ⟨1333365123045248815, 1335068543495824579⟩, true⟩

def words01 : List Nat := [371284938390234300, 371284938429309605, 371284938430736463, 371284938404890946, 371284937989208581, 371284937585821144, 371284937181497764, 371284937099452489, 371284936708094989, 371284936280234308]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 55710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 55700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477513010473872, 362477558281923147⟩, ⟨409402331664268583, 411106687425605721⟩, true⟩

def words02 : List Nat := [371284935851501705, 371284935745203926, 371284935513051040, 371284935538667280, 371284935540120531, 371284935516779054, 371284935279507065, 371284935122428667, 371284935037337194, 371284935039278712]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 55720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 55700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488473440089326, 362488518728590940⟩, ⟨(-201458297605941459), (-199752991427822569)⟩, true⟩

def words03 : List Nat := [371284934908324320, 371284934769759955, 371284934811369433, 371284934879332174, 371284935018592127, 371284935158581124, 371284935230299076, 371284935232178258, 371284935070181798, 371284935136774722]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 55730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 55700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477148665976702, 362477193971227257⟩, ⟨429834806703912935, 431541046552115283⟩, true⟩

def words04 : List Nat := [371284935336484227, 371284935338361097, 371284935169917423, 371284934966010128, 371284934761355646, 371284934655729307, 371284934490443858, 371284934553156058, 371284934615857573, 371284934617802183]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 55740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 55700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362492358982181541, 362492404304402415⟩, ⟨(-418157120857156777), (-416449934830048351)⟩, true⟩

def words05 : List Nat := [371284934648953630, 371284934819933719, 371284935279344783, 371284935357719944, 371284935359213030, 371284935341562481, 371284935517487861, 371284935552709472, 371284935687936751, 371284935824015944]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 55750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 55700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478238514125854, 362478283853296523⟩, ⟨369272321810051002, 370980453044757622⟩, true⟩

def words06 : List Nat := [371284935960033419, 371284935961943436, 371284936023925737, 371284936217072470, 371284936474746516, 371284936476623431, 371284936306167671, 371284936110869335, 371284935914821909, 371284935824841167]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 55760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 55700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362460741757820781, 362460787113861812⟩, ⟨1345236091776810365, 1346945163956866365⟩, true⟩

def words07 : List Nat := [371284935852349392, 371284935999871019, 371284936145719678, 371284936147597009, 371284935907242442, 371284935683308381, 371284935458347143, 371284935434073510, 371284935001908560, 371284934571085851]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 55770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 55700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362463847519424039, 362463892892277629⟩, ⟨1171963558596392444, 1173673568668638258⟩, true⟩

def words08 : List Nat := [371284934139470669, 371284933871093272, 371284933442978520, 371284933090540192, 371284932737509734, 371284932333313102, 371284931500620442, 371284930989763238, 371284930477973144, 371284930238910873]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 55780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 55700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474607053662095, 362474652443659719⟩, ⟨571656488676864080, 573367455297019514⟩, true⟩

def words09 : List Nat := [371284929863253561, 371284929487355530, 371284929110669519, 371284929055577192, 371284928867175805, 371284928777622911, 371284928687468971, 371284928531482365, 371284928027866183, 371284927846084397]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 55790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 55700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 55700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk557
