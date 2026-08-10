import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk545A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk545B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk545A

def state06 : KState := ⟨⟨362493389629183006, 362493432945819294⟩, ⟨(-467006473980324165), (-465409920850051125)⟩, true⟩

def words05 : List Nat := [371284903737900289, 371284903680280692, 371284903772291745, 371284903774124879, 371284903478571260, 371284903129923141, 371284902780556778, 371284902724876411, 371284902703233577, 371284902861677691]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 54550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 54500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475749075248233, 362475792408393698⟩, ⟨495487113460553920, 497084567417735526⟩, true⟩

def words06 : List Nat := [371284903011700331, 371284903013533671, 371284902752736084, 371284902791663519, 371284902845427186, 371284902847260665, 371284902453712656, 371284902039289460, 371284901624115923, 371284901526359939]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 54560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 54500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362460894203029794, 362460937552699842⟩, ⟨1306234184283559157, 1307832540071938245⟩, true⟩

def words07 : List Nat := [371284901360691075, 371284901307075815, 371284901252826594, 371284901199288143, 371284900824222589, 371284900477807981, 371284900130411398, 371284900118992289, 371284899743809895, 371284899306823550]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 54570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 54500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484804548096138, 362484847914171984⟩, ⟨1165431459931194, 2764682762277534⟩, true⟩

def words08 : List Nat := [371284898869055463, 371284898767430463, 371284898658971380, 371284898773785312, 371284898833860491, 371284898835727213, 371284898618621354, 371284898497650903, 371284898556763647, 371284898558662959]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 54580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 54500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473058998460299, 362473102381299741⟩, ⟨642416439576525489, 644016606083062645⟩, true⟩

def words09 : List Nat := [371284898559108102, 371284898555642748, 371284898584649308, 371284898586691632, 371284898453431804, 371284898394750255, 371284898335468906, 371284898276927034, 371284897770926470, 371284897557235329]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 54590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 54500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 54500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk545B
