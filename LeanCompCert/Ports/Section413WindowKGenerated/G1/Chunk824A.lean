import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk824A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362501568311772704, 362501670356599428⟩, ⟨(-1356926995236302529), (-1351249275964582779)⟩, true⟩

def state01 : KState := ⟨⟨362484989418851816, 362485091489433461⟩, ⟨9206296837770556, 14886138444535084⟩, true⟩

def words00 : List Nat := [371285272065002575, 371285272067857896, 371285272112554015, 371285272191616561, 371285272314281211, 371285272317136609, 371285272243632191, 371285272169303525, 371285272121271971, 371285272124531684]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479974918543374, 362480077014852911⟩, ⟨422479266202722818, 428161228174122676⟩, true⟩

def words01 : List Nat := [371285272172446858, 371285272223675810, 371285272273826244, 371285272276682383, 371285272148303558, 371285272056279294, 371285272001303371, 371285272004212635, 371285271945204770, 371285271885371889]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485170325107747, 362485272446942749⟩, ⟨(-5718580717997272), (-34514804847548)⟩, true⟩

def words02 : List Nat := [371285271908548527, 371285271939202147, 371285272018465993, 371285272098902374, 371285272137247072, 371285272140103286, 371285271981914474, 371285271957352751, 371285272025269198, 371285272028231284]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479735728312434, 362479837876273144⟩, ⟨442305022530146649, 447991242111564461⟩, true⟩

def words03 : List Nat := [371285272030389819, 371285272024747030, 371285272068672652, 371285272071842096, 371285272116386466, 371285272163239286, 371285272208899899, 371285272211757532, 371285272087573682, 371285272025255575]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473324488612495, 362473426662024049⟩, ⟨970878037365982109, 976566355247896345⟩, true⟩

def words04 : List Nat := [371285272003749059, 371285272006605863, 371285271855076566, 371285271704254808, 371285271552381920, 371285271408290850, 371285271224385837, 371285271152782157, 371285271080197974, 371285271008358166]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk824A
