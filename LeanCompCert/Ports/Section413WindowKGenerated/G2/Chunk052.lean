import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk052

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360701357930759423, 360701358068253324⟩, ⟨(-651252728191547961), (-651252242813428121)⟩, true⟩

def state01 : KState := ⟨⟨360911560921871421, 360911561059923249⟩, ⟨(-1746164214831107430), (-1746163726548987472)⟩, true⟩

def words00 : List Nat := [360576163891534083, 360576212025778415, 360576256993702589, 360576301944358776, 360576314494856022, 360576314985338798, 360576332820817007, 360576350649465260, 360576404874344182, 360576469191462496]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 5200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 5200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602955042980391, 360602955181595847⟩, ⟨(-136315658846336217), (-136315167624895981)⟩, true⟩

def words01 : List Nat := [360576514379909639, 360576559551025823, 360576614259060282, 360576697881196692, 360576754296948735, 360576810691081857, 360576841405104635, 360576841405163852, 360576841164741619, 360576846166536492]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 5210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 5200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360672968711999439, 360672968851174244⟩, ⟨(-502193332917915957), (-502192838773841427)⟩, true⟩

def words02 : List Nat := [360576864941783255, 360576885954824329, 360576888664069082, 360576891372283209, 360576891372333440, 360576866122464151, 360576902491918073, 360576938847472489, 360576947275821573, 360576965632138909]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 5220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 5200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361005560878219143, 361005561017954503⟩, ⟨(-2243110052104725657), (-2243109555026163231)⟩, true⟩

def words03 : List Nat := [360577020077153010, 360577074501375796, 360577164986882901, 360577219711410318, 360577242595357500, 360577265470571519, 360577324386649049, 360577404966112200, 360577486675330870, 360577568353381681]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 5230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 5200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360693512510447209, 360693512650749359⟩, ⟨(-608281588601684069), (-608281088550364207)⟩, true⟩

def words04 : List Nat := [360577631822330838, 360577659621822131, 360577683407076060, 360577707183276740, 360577721480453168, 360577721480512652, 360577720366925167, 360577691095290778, 360577661834798479, 360577671651215868]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 5240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 5200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360410195616666999, 360410195757530163⟩, ⟨881031867990845849, 881032370990373761⟩, true⟩

def words05 : List Nat := [360577712373390196, 360577753080071629, 360577767027821489, 360577767197911181, 360577767197961175, 360577758017020884, 360577748839556618, 360577738133166523, 360577724255470131, 360577692406007421]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 5250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 5200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360647531110358525, 360647531251785227⟩, ⟨(-368062453791700919), (-368061947825188947)⟩, true⟩

def words06 : List Nat := [360577664406097101, 360577686577152634, 360577722691480709, 360577758792102273, 360577764022176663, 360577764022236341, 360577734000033131, 360577717856445239, 360577701718968349, 360577703525011335]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 5260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 5200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360928406016450164, 360928406158447200⟩, ⟨(-1850712731846017715), (-1850712222870950441)⟩, true⟩

def words07 : List Nat := [360577703525065542, 360577688129213915, 360577692839749249, 360577731007368611, 360577758322306279, 360577785626901076, 360577795080065926, 360577826082014480, 360577892479804806, 360577958852468986]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 5270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 5200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360927889971212283, 360927890113772983⟩, ⟨(-1847792352788481749), (-1847791840834360953)⟩, true⟩

def words08 : List Nat := [360578060594344825, 360578150094050037, 360578220613646382, 360578291106562043, 360578335560255126, 360578398178361329, 360578470831698295, 360578543457573071, 360578591088978510, 360578657106622282]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 5280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 5200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360857255531556453, 360857255674685395⟩, ⟨(-1474782057345102253), (-1474781542382167693)⟩, true⟩

def words09 : List Nat := [360578704554787980, 360578751985043438, 360578818735743453, 360578850559563259, 360578851433644789, 360578852307401007, 360578888388356653, 360578942494278672, 360578995006249155, 360579047498420131]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 5290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 5200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 5200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk052
