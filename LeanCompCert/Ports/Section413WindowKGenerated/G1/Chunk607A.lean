import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk607A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471102945704395, 362471157017766124⟩, ⟨853757741371960795, 855974760525650443⟩, true⟩

def state01 : KState := ⟨⟨362483806118142017, 362483860208603857⟩, ⟨82679166363146154, 84897302497569146⟩, true⟩

def words00 : List Nat := [371285258512719951, 371285258509922724, 371285258531309996, 371285258679426715, 371285258800252011, 371285258802308304, 371285258592763506, 371285258554815735, 371285258613688078, 371285258615826680]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 60700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 60700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492267725704625, 362492321834943110⟩, ⟨(-431084449519830982), (-428865173364264922)⟩, true⟩

def words01 : List Nat := [371285258594357689, 371285258507888337, 371285258574770982, 371285258595688681, 371285258697468529, 371285258800014653, 371285258870786641, 371285258872879066, 371285258835420469, 371285258954335672]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 60710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 60700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484485308194060, 362484539435723875⟩, ⟨41514868532320397, 43735255432619479⟩, true⟩

def words02 : List Nat := [371285259275783742, 371285259277840619, 371285259268847039, 371285259257603784, 371285259245607539, 371285259238083679, 371285259274972904, 371285259430679079, 371285259592584186, 371285259594713380]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 60720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 60700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500824414910852, 362500878561041309⟩, ⟨(-950835375601879728), (-948613858990971238)⟩, true⟩

def words03 : List Nat := [371285259710623555, 371285259839487122, 371285260238620568, 371285260276957531, 371285260278549362, 371285260275635458, 371285260538014146, 371285260686456360, 371285260945003007, 371285261204412493]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 60730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 60700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489974477595839, 362490028642301540⟩, ⟨(-291802567342262781), (-289579922377147237)⟩, true⟩

def words04 : List Nat := [371285261424462230, 371285261426533674, 371285261521747962, 371285261636118672, 371285261831065856, 371285261833159212, 371285261803968904, 371285261774686135, 371285261892234293, 371285261973071781]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 60740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 60700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk607A
