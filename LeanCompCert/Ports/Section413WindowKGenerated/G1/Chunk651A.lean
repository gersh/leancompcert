import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk651A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490831613057321, 362490894152369124⟩, ⟨(-352276969615294434), (-349527126401993970)⟩, true⟩

def state01 : KState := ⟨⟨362478048677903466, 362478111236950655⟩, ⟨480009385052430371, 482760513142075899⟩, true⟩

def words00 : List Nat := [371285525474241330, 371285525520184462, 371285525565465789, 371285525611534600, 371285525702428523, 371285525704894154, 371285525723597548, 371285525771496763, 371285525773165360, 371285525774089990]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 65100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 65100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502491018128053, 362502553597235627⟩, ⟨(-1111551710197278683), (-1108799275874610343)⟩, true⟩

def words01 : List Nat := [371285525783501717, 371285525907953301, 371285526132759143, 371285526162392910, 371285526164124824, 371285526154423885, 371285526287499975, 371285526315807705, 371285526578787379, 371285526842795821]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 65110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 65100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489241043738959, 362489303642865189⟩, ⟨(-248713669623351760), (-245959931584503640)⟩, true⟩

def words02 : List Nat := [371285527062227462, 371285527064444969, 371285527108810897, 371285527250688179, 371285527461498441, 371285527463715993, 371285527360555736, 371285527227749963, 371285527194268357, 371285527254792160]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 65120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 65100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472325055027717, 362472387674080231⟩, ⟨853152011224076176, 855907047163961972⟩, true⟩

def words03 : List Nat := [371285527412054352, 371285527570187425, 371285527727445110, 371285527729665116, 371285527632091202, 371285527546066327, 371285527571269544, 371285527573487709, 371285527373588025, 371285527174343725]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 65130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 65100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479447768509416, 362479510407442587⟩, ⟨389240507105568415, 391996838171032625⟩, true⟩

def words04 : List Nat := [371285527007909143, 371285527010436941, 371285527134326520, 371285527275766325, 371285527370037259, 371285527372255655, 371285527166528998, 371285527183256815, 371285527240725533, 371285527243024645]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 65140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 65100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk651A
