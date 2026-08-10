import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk648A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486660972392313, 362486722914122806⟩, ⟨(-79117748487228664), (-76406718348062456)⟩, true⟩

def state01 : KState := ⟨⟨362471919921007248, 362471981882369165⟩, ⟨876163635473136354, 878875937832798214⟩, true⟩

def words00 : List Nat := [371285543916453163, 371285543918658727, 371285543701739791, 371285543485307370, 371285543268058333, 371285543095050678, 371285542834544212, 371285542790113015, 371285542744938305, 371285542689927147]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 64800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 64800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362495700349983650, 362495762331298598⟩, ⟨(-665177357672678391), (-662463762055617969)⟩, true⟩

def words01 : List Nat := [371285542510873966, 371285542542192574, 371285542654914105, 371285542657123415, 371285542512848148, 371285542317325654, 371285542160836143, 371285542163301683, 371285542276931048, 371285542437096787]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 64810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 64800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362469639687059439, 362469701688252935⟩, ⟨1024134423266878380, 1026849307512393132⟩, true⟩

def words02 : List Nat := [371285542556529151, 371285542558735623, 371285542360997123, 371285542257615463, 371285542153127029, 371285542120258424, 371285541769896741, 371285541373631055, 371285540976495117, 371285540795263770]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 64820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 64800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362471356942711380, 362471418963797888⟩, ⟨912852128417382510, 915568302430891848⟩, true⟩

def words03 : List Nat := [371285540552454191, 371285540467454548, 371285540381681254, 371285540296357744, 371285540079190294, 371285539935707573, 371285539817021995, 371285539819235021, 371285539603233888, 371285539387956292]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 64830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 64800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472965581144037, 362473027622020578⟩, ⟨808544467506727091, 811261924804745853⟩, true⟩

def words04 : List Nat := [371285539171710109, 371285539018544112, 371285538752869329, 371285538690875440, 371285538628229879, 371285538493404370, 371285538041114144, 371285537763264838, 371285537484204200, 371285537443528747]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 64840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 64800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk648A
