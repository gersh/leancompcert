import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk193A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360425216313864134, 360425218469076148⟩, ⟨3066946873648573609, 3066975025881844451⟩, true⟩

def state01 : KState := ⟨⟨360588791875105272, 360588794032645417⟩, ⟨(-90863349887691267), (-90835152709987883)⟩, true⟩

def words00 : List Nat := [360584120859094111, 360584115293730383, 360584111096097489, 360584108755068694, 360584106414267371, 360584101474555928, 360584096709432252, 360584093579679703, 360584090450179547, 360584090228973418]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 19300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 19300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568640139328319, 360568642299223820⟩, ⟨298133397301896941, 298161639972774861⟩, true⟩

def words01 : List Nat := [360584090229193403, 360584088683977473, 360584087138877421, 360584084725103387, 360584084294467424, 360584083190527532, 360584082086673481, 360584079356122402, 360584075894877967, 360584075096323861]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 19310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 19300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360490245747299145, 360490247909518341⟩, ⟨1813177665613360363, 1813205953190028925⟩, true⟩

def words02 : List Nat := [360584075799950589, 360584075800197623, 360584074634605170, 360584071855520841, 360584069076684212, 360584065576873312, 360584063438037835, 360584059795863816, 360584056154040297, 360584050597215705]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 19320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 19300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360624269070052586, 360624271234604017⟩, ⟨(-778332291766621197), (-778303959096055627)⟩, true⟩

def words03 : List Nat := [360584045744967899, 360584041651092652, 360584037557566333, 360584036123343052, 360584034802711102, 360584031190999871, 360584027579615158, 360584025928853226, 360584028009989577, 360584030090966354]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 19330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 19300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360556240191224310, 360556242358137095⟩, ⟨537281090088698325, 537309468439089333⟩, true⟩

def words04 : List Nat := [360584030091192410, 360584030080387835, 360584028979656934, 360584028148273431, 360584027316909501, 360584025257096435, 360584022412525567, 360584018235272783, 360584014058401802, 360584010289322578]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 19340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 19300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk193A
