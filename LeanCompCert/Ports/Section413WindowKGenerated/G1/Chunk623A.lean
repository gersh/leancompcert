import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk623A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362501387640451590, 362501444717967960⟩, ⟨(-1000893028215306327), (-998491162161972461)⟩, true⟩

def state01 : KState := ⟨⟨362479640935915453, 362479698032503782⟩, ⟨354003295343785778, 356406349674185600⟩, true⟩

def words00 : List Nat := [371285418085017255, 371285418087131603, 371285418166930606, 371285418337597116, 371285418529602749, 371285418531717190, 371285418380495843, 371285418171677713, 371285417962030874, 371285417922564354]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 62300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 62300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362474382762909817, 362474439878548292⟩, ⟨681753050209997926, 684157291651264094⟩, true⟩

def words01 : List Nat := [371285417998167930, 371285418166441185, 371285418332966701, 371285418335118431, 371285418287941477, 371285418239242939, 371285418357481720, 371285418359596674, 371285418185989672, 371285418012239744]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 62310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 62300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495188675030358, 362495245809632059⟩, ⟨(-614977310916545640), (-612571887593105068)⟩, true⟩

def words02 : List Nat := [371285417837546109, 371285417720002085, 371285417604582493, 371285417677260312, 371285417710709183, 371285417712838860, 371285417575048836, 371285417636851407, 371285417925398487, 371285418085263878]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 62320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 62300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486003704423371, 362486060858264075⟩, ⟨(-42377055629060776), (-39970433038918322)⟩, true⟩

def words03 : List Nat := [371285418242878875, 371285418401183795, 371285418790980482, 371285419052836020, 371285419308796060, 371285419565555275, 371285419774257044, 371285419776373196, 371285419687347911, 371285419700229413]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 62330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 62300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488700864920723, 362488758037628391⟩, ⟨(-210489833931421071), (-208082035077069843)⟩, true⟩

def words04 : List Nat := [371285419925394474, 371285419974170231, 371285420020834216, 371285420068213682, 371285420154511823, 371285420156843749, 371285420329163358, 371285420545640829, 371285420713297947, 371285420769018793]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 62340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 62300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk623A
