import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk090

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362409037315496313, 362409038325037082⟩, ⟨657248600031647763, 657254752252953649⟩, true⟩

def state01 : KState := ⟨⟨362453802422179847, 362453803434048732⟩, ⟨254495960270567118, 254502133456992222⟩, true⟩

def words00 : List Nat := [371282062703667950, 371282062703933257, 371282056771509882, 371282050855377321, 371282044940462047, 371282042790674587, 371282042044349826, 371282047810774238, 371282050063462292, 371282050063733193]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 9000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 9000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362624301928978366, 362624302943205703⟩, ⟨(-1282380555129615399), (-1282374360681544953)⟩, true⟩

def words01 : List Nat := [371282056065560995, 371282065200175640, 371282086600239676, 371282091646932814, 371282094507705745, 371282097367932436, 371282110155479593, 371282117072829071, 371282132836407398, 371282148596605377]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 9010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 9000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362503506573422396, 362503507590013144⟩, ⟨(-192594586132778505), (-192588370354867281)⟩, true⟩

def words02 : List Nat := [371282163498479756, 371282166830216080, 371282175157867979, 371282183483809297, 371282194710624313, 371282194710886038, 371282189632627182, 371282182337932872, 371282179973945331, 371282182335849168]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 9020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 9000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362318267714427490, 362318268733378006⟩, ⟨1481500710853093208, 1481506947951994994⟩, true⟩

def words03 : List Nat := [371282190767113899, 371282199196618571, 371282207638516406, 371282207638778543, 371282199806255156, 371282194013832171, 371282188222559868, 371282187428068504, 371282170375735010, 371282152245319599]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 9030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 9000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362469493768071377, 362469494789372064⟩, ⟨114061088215073533, 114067346571196805⟩, true⟩

def words04 : List Nat := [371282134118796194, 371282128182113874, 371282120076549668, 371282122115539233, 371282122115744569, 371282121685545856, 371282105021256710, 371282098930269959, 371282098915793119, 371282098916065014]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 9040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 9000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362501311622295904, 362501312645988129⟩, ⟨(-174250904328740834), (-174244624316824092)⟩, true⟩

def words05 : List Nat := [371282097523697668, 371282093674409806, 371282092061576922, 371282092061868644, 371282088305093820, 371282088276536051, 371282088247893136, 371282088239574522, 371282080347176961, 371282082470034391]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 9050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 9000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362393078372622036, 362393079398655105⟩, ⟨806831637525856098, 806837938758082666⟩, true⟩

def words06 : List Nat := [371282087826162993, 371282087826426384, 371282080478546124, 371282072729920937, 371282064982904561, 371282056797206906, 371282042540939489, 371282040410918440, 371282038281281355, 371282036172498334]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 9060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 9000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362516319349316161, 362516320377736715⟩, ⟨(-311356657974822024), (-311350335076497876)⟩, true⟩

def words07 : List Nat := [371282026585000111, 371282026804322346, 371282036617893199, 371282036618157750, 371282035031590550, 371282029781613543, 371282028095158383, 371282028095449097, 371282030692959265, 371282034469238037]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 9070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 9000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362502981885868365, 362502982916670173⟩, ⟨(-190473579328980122), (-190467234796791958)⟩, true⟩

def words08 : List Nat := [371282038111166323, 371282038111430496, 371282030977530573, 371282032466277605, 371282035286155838, 371282035286425918, 371282031756970484, 371282027856382902, 371282029425190309, 371282031730354390]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 9080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 9000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362358699871334619, 362358700904513448⟩, ⟨1122355455225534764, 1122361821377079952⟩, true⟩

def words09 : List Nat := [371282046085477961, 371282060437548282, 371282072377828990, 371282072378093058, 371282068256628300, 371282064899619547, 371282064255571047, 371282064255835212, 371282050923047955, 371282037368401040]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 9090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 9000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 9000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk090
