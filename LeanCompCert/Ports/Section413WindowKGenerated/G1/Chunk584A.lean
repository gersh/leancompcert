import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk584A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494931989671667, 362494981888458394⟩, ⟨(-584556534603477079), (-582588067587776609)⟩, true⟩

def state01 : KState := ⟨⟨362486609126456754, 362486659043076760⟩, ⟨(-98528818952123086), (-96559310383444464)⟩, true⟩

def words00 : List Nat := [371285006347019095, 371285006348991575, 371285006080517661, 371285006094716387, 371285006195972440, 371285006197951622, 371285006078936256, 371285005959477888, 371285005911011436, 371285005941599582]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 58400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 58400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476262425636156, 362476312359967840⟩, ⟨505952238620810032, 507922781821655414⟩, true⟩

def words01 : List Nat := [371285006264657593, 371285006588494524, 371285006910539752, 371285006912512654, 371285006843679427, 371285006793606629, 371285006983393070, 371285006985366061, 371285006836992035, 371285006690365335]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 58410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 58400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477807510976397, 362477857462994827⟩, ⟨415748430651644656, 417720007201455344⟩, true⟩

def words02 : List Nat := [371285006542891438, 371285006512397858, 371285006527515920, 371285006650151285, 371285006723776459, 371285006725750033, 371285006452014391, 371285006463482428, 371285006528335286, 371285006530378046]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 58420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 58400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481288729263670, 362481338699276866⟩, ⟨212337705081910529, 214310333156844733⟩, true⟩

def words03 : List Nat := [371285006409502900, 371285006288180381, 371285006294469883, 371285006296644629, 371285006291936217, 371285006305248867, 371285006306738905, 371285006299871931, 371285005945281710, 371285005884991392]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 58430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 58400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476794719675034, 362476844707305738⟩, ⟨474987716634502926, 476961374366113178⟩, true⟩

def words04 : List Nat := [371285006053987057, 371285006055961047, 371285005897425725, 371285005639743370, 371285005381327700, 371285005211605706, 371285004925164149, 371285004906647817, 371285004887430116, 371285004867688392]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 58440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 58400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk584A
