import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk731A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362505741731090147, 362505821302678760⟩, ⟨(-1503964344307473546), (-1500036154893432796)⟩, true⟩

def state01 : KState := ⟨⟨362493214211377959, 362493293805636709⟩, ⟨(-588199764440631702), (-584269917721004298)⟩, true⟩

def words00 : List Nat := [371285301490262510, 371285301492773660, 371285301609602983, 371285301741709216, 371285301929295588, 371285301950023625, 371285301969272368, 371285301989376197, 371285302147489489, 371285302259662492]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 73100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 73100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362473050777585220, 362473130394477269⟩, ⟨886134345959822901, 890065847514330579⟩, true⟩

def words01 : List Nat := [371285302546638277, 371285302834671068, 371285303122248564, 371285303179238070, 371285303243819649, 371285303309613879, 371285303393615135, 371285303396126763, 371285303231066087, 371285303067446557]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 73110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 73100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485181424815526, 362485261064208060⟩, ⟨(-845374509285956), 3087772395455612⟩, true⟩

def words02 : List Nat := [371285302923087162, 371285302925903099, 371285303002621499, 371285303127108390, 371285303233545915, 371285303236057823, 371285303135214148, 371285303180411034, 371285303284667452, 371285303287268302]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 73120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 73100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491898013437977, 362491977675703607⟩, ⟨(-492035181894433212), (-488100362166333424)⟩, true⟩

def words03 : List Nat := [371285303288572814, 371285303283854214, 371285303457534671, 371285303562464780, 371285303723101338, 371285303884776959, 371285304045973946, 371285304071831468, 371285304164791754, 371285304259122397]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 73130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 73100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491384575392565, 362491464260051882⟩, ⟨(-454488347785494074), (-450551890069149372)⟩, true⟩

def words04 : List Nat := [371285304538845297, 371285304570307201, 371285304572238843, 371285304562611743, 371285304596379479, 371285304599148760, 371285304703181164, 371285304844387606, 371285304969749335, 371285305056622413]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 73140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 73100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk731A
