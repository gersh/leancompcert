import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk942A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483165601461153, 362483300350443667⟩, ⟨167045681248383377, 175615816133590921⟩, true⟩

def state01 : KState := ⟨⟨362487507625282008, 362487642403644223⟩, ⟨(-241965321929746704), (-233392419325848492)⟩, true⟩

def words00 : List Nat := [371285164712631983, 371285164715940519, 371285164717654797, 371285164720889649, 371285164748146847, 371285164751846409, 371285164835452181, 371285164936130736, 371285165036686057, 371285165066397768]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 94200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 94200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498952132571377, 362499086940750482⟩, ⟨(-1320234988373334096), (-1311659276567264328)⟩, true⟩

def words01 : List Nat := [371285165169451511, 371285165274205660, 371285165411425803, 371285165439504474, 371285165442074493, 371285165432842646, 371285165507857358, 371285165546554246, 371285165696545379, 371285165848036891]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 94210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 94200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492281865951621, 362492416703922620⟩, ⟨(-691775230065372717), (-683196711117803833)⟩, true⟩

def words02 : List Nat := [371285165990146725, 371285165993446652, 371285166066982501, 371285166152814533, 371285166271403717, 371285166290261935, 371285166292771653, 371285166289285721, 371285166390120503, 371285166470866431]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 94220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 94200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479064503782180, 362479199371489640⟩, ⟨553807053366256476, 562388374530527902⟩, true⟩

def words03 : List Nat := [371285166592896541, 371285166716288444, 371285166832600794, 371285166870573418, 371285166934091501, 371285166999205461, 371285167097693846, 371285167100994299, 371285167049621737, 371285166990064880]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 94230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 94200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487928615056189, 362488063512366385⟩, ⟨(-281598751190620070), (-273014640124748910)⟩, true⟩

def words04 : List Nat := [371285166929018551, 371285166916066157, 371285166885945688, 371285166923822438, 371285166936653363, 371285166939954166, 371285166802411974, 371285166768344612, 371285166801868484, 371285166836043325]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 94240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 94200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk942A
