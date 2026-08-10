import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk754A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360539583648482717, 360539620506499186⟩, ⟨3209770787383876977, 3211647845039761675⟩, true⟩

def state01 : KState := ⟨⟨360580983274160252, 360581020142304774⟩, ⟨88061576107053841, 89939397469122195⟩, true⟩

def words00 : List Nat := [360582214741463059, 360582214353455095, 360582214082481447, 360582213987427131, 360582213892280091, 360582213624626061, 360582213257184852, 360582213065739707, 360582212873984726, 360582212814330621]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 75400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 75400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360578687614614106, 360578724493015156⟩, ⟨261139585024379933, 263018179880695839⟩, true⟩

def words01 : List Nat := [360582212799501215, 360582212644159669, 360582212488617946, 360582212385598237, 360582212370615817, 360582212311359102, 360582212251981151, 360582212082210242, 360582211917757106, 360582211872753697]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 75410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 75400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360571222896917571, 360571259785432449⟩, ⟨824167582925987343, 826046940617747179⟩, true⟩

def words02 : List Nat := [360582211929376853, 360582211930451453, 360582211924267416, 360582211818443677, 360582211712464462, 360582211482690027, 360582211365504874, 360582211275808802, 360582211186010488, 360582210957918433]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 75420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 75400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360588617011236111, 360588653909908534⟩, ⟨(-487931690393961890), (-486051566469753224)⟩, true⟩

def words03 : List Nat := [360582210843972881, 360582210875543580, 360582211051333660, 360582211052408003, 360582211052697575, 360582210901474325, 360582210773273711, 360582210933231509, 360582211019524981, 360582211106042338]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 75430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 75400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581766990517068, 360581803899416173⟩, ⟨28793959883042922, 30674855358861240⟩, true⟩

def words04 : List Nat := [360582211106999832, 360582211105537579, 360582210984637802, 360582210965616570, 360582210946311390, 360582210857830193, 360582210844979117, 360582210728374972, 360582210611576026, 360582210458135310]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 75440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 75400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk754A
