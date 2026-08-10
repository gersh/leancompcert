import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk617A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362513214906814460, 362513270847440634⟩, ⟨(-1723640632524369968), (-1721309254329466064)⟩, true⟩

def state01 : KState := ⟨⟨362491748942182898, 362491804901670373⟩, ⟨(-399131638503474596), (-396799096470258894)⟩, true⟩

def words00 : List Nat := [371285373699140545, 371285373792075103, 371285374147261683, 371285374503563235, 371285374825210432, 371285374827303428, 371285374798901816, 371285374750867767, 371285374837739439, 371285374944345581]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 61700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 61700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476317818737940, 362476373797100026⟩, ⟨553254065984617592, 555587772865370420⟩, true⟩

def words01 : List Nat := [371285375171389990, 371285375399345529, 371285375627439883, 371285375629533482, 371285375542262143, 371285375535057567, 371285375779913148, 371285375782006508, 371285375686738046, 371285375543257923]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 61710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 61700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491756295160861, 362491812292266379⟩, ⟨(-399670290943795050), (-397335427122955276)⟩, true⟩

def words02 : List Nat := [371285375398842942, 371285375367155246, 371285375316472203, 371285375424070620, 371285375485829428, 371285375487959473, 371285375340317979, 371285375351118709, 371285375623533253, 371285375729969917]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 61720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 61700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487363698371725, 362487419714571419⟩, ⟨(-128483279384461293), (-126147236785750791)⟩, true⟩

def words03 : List Nat := [371285375828201160, 371285375927117964, 371285376133112675, 371285376209241755, 371285376363549476, 371285376518672665, 371285376672108706, 371285376674202662, 371285376510818122, 371285376546550400]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 61730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 61700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472111870197166, 362472167905040671⟩, ⟨813239253849061990, 815576447612883440⟩, true⟩

def words04 : List Nat := [371285376775241812, 371285376777335847, 371285376656472827, 371285376487231824, 371285376317161251, 371285376207555991, 371285375979967852, 371285375861128657, 371285375741620552, 371285375620791487]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 61740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 61700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk617A
