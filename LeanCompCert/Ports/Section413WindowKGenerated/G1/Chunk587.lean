import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk587

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502587417749590, 362502637850973650⟩, ⟨(-1035560242475294909), (-1033560484044322525)⟩, true⟩

def state01 : KState := ⟨⟨362483903340578361, 362483953791715688⟩, ⟨61281737938744353, 63282547969939235⟩, true⟩

def words00 : List Nat := [371285030915340255, 371285030945926541, 371285031219619967, 371285031494357526, 371285031829448799, 371285031831432235, 371285031809871819, 371285031725571694, 371285031673079523, 371285031675346585]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 58700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 58700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487751785590112, 362487802254611829⟩, ⟨(-164617331606939625), (-162615471493063427)⟩, true⟩

def words01 : List Nat := [371285031930372742, 371285032204573913, 371285032477136691, 371285032479122013, 371285032456660779, 371285032490584412, 371285032774108681, 371285032866657857, 371285032915306426, 371285032964724173]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 58710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 58700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487112544488979, 362487163031277513⟩, ⟨(-127042479966497335), (-125039576492288965)⟩, true⟩

def words02 : List Nat := [371285033204887457, 371285033301449429, 371285033516235844, 371285033731780846, 371285033895429153, 371285033897413346, 371285033739940736, 371285033808027041, 371285033971185287, 371285034009525929]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 58720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 58700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491843293062631, 362491893797902434⟩, ⟨(-404871629416296711), (-402867665698485003)⟩, true⟩

def words03 : List Nat := [371285034046349331, 371285034083823267, 371285034410659703, 371285034630616879, 371285034880166343, 371285035130489006, 371285035326710091, 371285035328695453, 371285035306078998, 371285035425288783]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 58730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 58700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487145206604689, 362487195729102351⟩, ⟨(-128840802982918851), (-126835801950154179)⟩, true⟩

def words04 : List Nat := [371285035833483633, 371285035930722528, 371285036005638020, 371285036081261984, 371285036229349724, 371285036233916619, 371285036429217051, 371285036625298338, 371285036819777236, 371285036858581847]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 58740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 58700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362505635122581285, 362505685663079439⟩, ⟨(-1215275867204134434), (-1213269808556805634)⟩, true⟩

def words05 : List Nat := [371285036924512543, 371285036991496698, 371285037273468882, 371285037275455818, 371285037245399650, 371285037171840195, 371285037311753017, 371285037421611415, 371285037774357955, 371285038128004189]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 58750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 58700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489329437083610, 362489379995491070⟩, ⟨(-257081891468823806), (-255074780377825466)⟩, true⟩

def words06 : List Nat := [371285038481483056, 371285038576995144, 371285038961746375, 371285039347492265, 371285039709768032, 371285039711753791, 371285039687988116, 371285039656997895, 371285039772337890, 371285039848473361]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 58760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 58700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474486785345339, 362474537361624400⟩, ⟨615384547214871577, 617392708712100943⟩, true⟩

def words07 : List Nat := [371285040213477260, 371285040579295613, 371285040890040071, 371285040892026068, 371285040828391895, 371285040842516038, 371285041106499790, 371285041108485841, 371285040986706503, 371285040810224470]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 58770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 58700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362507570568761394, 362507621162833004⟩, ⟨(-1329433031528479779), (-1327423824096929157)⟩, true⟩

def words08 : List Nat := [371285040689851843, 371285040692040602, 371285040742995233, 371285040877082702, 371285040966636442, 371285040968677031, 371285041236394394, 371285041516760696, 371285042085694237, 371285042471807219]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 58780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 58700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492518080133720, 362492568692344048⟩, ⟨(-444399170133406669), (-442388896238500121)⟩, true⟩

def words09 : List Nat := [371285042856386340, 371285043241640608, 371285043690894508, 371285044009691582, 371285044343244020, 371285044677518412, 371285045001268976, 371285045003255993, 371285045069124950, 371285045199610277]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 58790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 58700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 58700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk587
