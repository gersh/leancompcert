import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk605A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362511229540797168, 362511283243078811⟩, ⟨(-1577580848074852582), (-1575386237646006930)⟩, true⟩

def state01 : KState := ⟨⟨362496669119658325, 362496722840425546⟩, ⟨(-696671353551979970), (-694475624649153116)⟩, true⟩

def words00 : List Nat := [371285244580391837, 371285244679221345, 371285244949056848, 371285245219959288, 371285245571984540, 371285245574033421, 371285245561976196, 371285245550946026, 371285245799175386, 371285245991180795]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 60500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 60500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477177121117055, 362477230860347413⟩, ⟨482933924324767115, 485130770523645815⟩, true⟩

def words01 : List Nat := [371285246321280762, 371285246652224818, 371285246962324615, 371285246964374029, 371285246946361356, 371285246937073930, 371285247159075757, 371285247161125019, 371285247030966689, 371285246900838551]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 60510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 60500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492457485212194, 362492511242814257⟩, ⟨(-441821222399892534), (-439623264253462974)⟩, true⟩

def words02 : List Nat := [371285246910595910, 371285246985182282, 371285247260971624, 371285247537565788, 371285247770106258, 371285247772156436, 371285247863266735, 371285248047223870, 371285248341894472, 371285248464002517]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 60520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 60500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492253425981329, 362492307202227396⟩, ⟨(-429455335795738990), (-427256249033772260)⟩, true⟩

def words03 : List Nat := [371285248584751920, 371285248706171995, 371285248965777845, 371285249124959174, 371285249365421603, 371285249606722236, 371285249815521170, 371285249817571157, 371285249779014233, 371285249898102361]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 60530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 60500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484261790833625, 362484315585362050⟩, ⟨54380586922301623, 56580780591327523⟩, true⟩

def words04 : List Nat := [371285250196326180, 371285250198376325, 371285250133036157, 371285250029880261, 371285249925897296, 371285249904893471, 371285249840567095, 371285249936218169, 371285250030443807, 371285250032605508]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 60540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 60500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk605A
