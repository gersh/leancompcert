import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk458A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598856490769418, 360598869555589059⟩, ⟨(-717953421807486532), (-717549068754776868)⟩, true⟩

def state01 : KState := ⟨⟨360576646619658496, 360576659690468013⟩, ⟨299173244735404133, 299577872154137623⟩, true⟩

def words00 : List Nat := [360583202887995554, 360583202861357121, 360583202359023629, 360583202227094632, 360583202095000721, 360583201842156204, 360583201324163554, 360583200567418154, 360583199810575953, 360583199264188907]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 45800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 45800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360534092119376748, 360534105196097901⟩, ⟨2248862536540642669, 2249267434800860173⟩, true⟩

def words01 : List Nat := [360583199310166098, 360583199499009233, 360583199499568770, 360583199449701137, 360583198924419372, 360583197893061767, 360583196861564275, 360583196305653773, 360583195473166137, 360583194402444494]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 45810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 45800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599380441902140, 360599393524560729⟩, ⟨(-742860366552408701), (-742455196209560123)⟩, true⟩

def words02 : List Nat := [360583193331626901, 360583192736411025, 360583192750343257, 360583192995347093, 360583192995929804, 360583192832978669, 360583192846383907, 360583193091164917, 360583193323251457, 360583193677378483]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 45820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 45800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360609425087702325, 360609438176340739⟩, ⟨(-1203266085815276882), (-1202860641387050250)⟩, true⟩

def words03 : List Nat := [360583193792901058, 360583193908488838, 360583194499088550, 360583195328784385, 360583195948656127, 360583196568614023, 360583196830870935, 360583197187280320, 360583197760236476, 360583198333375118]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 45830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 45800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596712785404855, 360596725879970306⟩, ⟨(-620522326353797064), (-620116610201677192)⟩, true⟩

def words04 : List Nat := [360583199381271428, 360583199954532943, 360583200097677117, 360583200240873694, 360583200241399830, 360583200368525956, 360583200699811466, 360583201031205865, 360583201031768204, 360583201276140473]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 45840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 45800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk458A
