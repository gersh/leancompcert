import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk613A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476647727942989, 362476702917210464⟩, ⟨526739541952517438, 529024711349952980⟩, true⟩

def state01 : KState := ⟨⟨362493373900582434, 362493429108444782⟩, ⟨(-498625628154322735), (-496339318797612575)⟩, true⟩

def words00 : List Nat := [371285332948430938, 371285332950726925, 371285333025557440, 371285333132510364, 371285333174525453, 371285333176641923, 371285333139509210, 371285333235074027, 371285333537563961, 371285333671756462]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 61300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 61300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493789070207222, 362493844297055905⟩, ⟨(-524080259018859037), (-521792785516453239)⟩, true⟩

def words01 : List Nat := [371285333803686337, 371285333936343218, 371285334142972429, 371285334257552815, 371285334451417794, 371285334646053515, 371285334839806518, 371285334841890827, 371285334953492355, 371285335094898138]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 61310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 61300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467730287384336, 362467785532729285⟩, ⟨1073986188009164890, 1076274795801731506⟩, true⟩

def words02 : List Nat := [371285335362766797, 371285335364845858, 371285335278415749, 371285335191968674, 371285335104758891, 371285335013832488, 371285334789302824, 371285334675071342, 371285334560114667, 371285334445101725]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 61320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 61300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362510830155379320, 362510885419493526⟩, ⟨(-1569527322121196990), (-1567237563115155264)⟩, true⟩

def words03 : List Nat := [371285334160377705, 371285334142714180, 371285334369841336, 371285334461076993, 371285334506487496, 371285334552567859, 371285334837145021, 371285334990048750, 371285335407997138, 371285335826837470]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 61330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 61300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494255985903956, 362494311268815756⟩, ⟨(-552844273108751165), (-550553360965811095)⟩, true⟩

def words04 : List Nat := [371285336180350942, 371285336182430678, 371285336445190647, 371285336711347927, 371285337056530216, 371285337094555636, 371285337096128419, 371285337088937528, 371285337291527100, 371285337440174564]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 61340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 61300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk613A
