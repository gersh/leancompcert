import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk310A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360519882021505222, 360519887817780987⟩, ⟨1956155930248652190, 1956277442548875722⟩, true⟩

def state01 : KState := ⟨⟨360547582618716618, 360547588418887197⟩, ⟨1097236162170879124, 1097357795229307742⟩, true⟩

def words00 : List Nat := [360582991506464851, 360582990028307359, 360582989075662644, 360582987781117444, 360582986486628372, 360582984283245048, 360582981532229337, 360582979515136279, 360582977498052958, 360582975642209652]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 31000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 31000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569681442679835, 360569687246772161⟩, ⟨411805979918394508, 411927734609930980⟩, true⟩

def words01 : List Nat := [360582974501458401, 360582972844794771, 360582971188159252, 360582970567034923, 360582970464830127, 360582970099437971, 360582969734030857, 360582968561231568, 360582967098474124, 360582966670840825]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 31010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 31000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360533444456142331, 360533450264112033⟩, ⟨1535997128175105998, 1536119003162532658⟩, true⟩

def words02 : List Nat := [360582966538655038, 360582966539067225, 360582965798620320, 360582964519200094, 360582963239789478, 360582961281922402, 360582959848663719, 360582958264984253, 360582956681361938, 360582954582615499]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 31020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 31000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567856442688361, 360567862254554723⟩, ⟨467721988019851917, 467843983940108521⟩, true⟩

def words03 : List Nat := [360582952987640665, 360582950558146518, 360582948128684257, 360582946733377088, 360582944705829796, 360582941788247118, 360582938870773809, 360582936551936759, 360582935033017035, 360582934547851763]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 31030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 31000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586510192445534, 360586516008244537⟩, ⟨(-111572333261214741), (-111450215253791869)⟩, true⟩

def words04 : List Nat := [360582934062661838, 360582933047006363, 360582932418111844, 360582932372148645, 360582932326083253, 360582931565343480, 360582930612393526, 360582929046654196, 360582927480936960, 360582926744927614]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 31040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 31000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk310A
