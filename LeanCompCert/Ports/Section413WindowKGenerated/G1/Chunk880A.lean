import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk880A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478325413197498, 362478442391074593⟩, ⟨587476342578676914, 594426852503106088⟩, true⟩

def state01 : KState := ⟨⟨362491226276876600, 362491343282174967⟩, ⟨(-547819876039306547), (-540866952901662425)⟩, true⟩

def words00 : List Nat := [371285197219252995, 371285197222663058, 371285197329142046, 371285197449205437, 371285197547669995, 371285197550735941, 371285197560363600, 371285197632347225, 371285197761966158, 371285197834981984]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 88000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 88000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496305091855800, 362496422125096280⟩, ⟨(-994850971699623515), (-987895589233080241)⟩, true⟩

def words01 : List Nat := [371285197863574523, 371285197893096449, 371285198042820258, 371285198129357758, 371285198237320996, 371285198346495179, 371285198454611794, 371285198457731373, 371285198585855279, 371285198717168251]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 88010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 88000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485016468014987, 362485133528540744⟩, ⟨(-1153394652876484), 5804389606915340⟩, true⟩

def words02 : List Nat := [371285198913032887, 371285198994194542, 371285199057462432, 371285199121779611, 371285199192004318, 371285199210048378, 371285199293402266, 371285199377970293, 371285199461860442, 371285199465035200]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 88020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 88000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493393003005960, 362493510091327378⟩, ⟨(-738579761693703655), (-731619530446821147)⟩, true⟩

def words03 : List Nat := [371285199574701470, 371285199686814183, 371285199846285373, 371285199849352084, 371285199837149076, 371285199805345540, 371285199866123518, 371285199910352395, 371285200006859287, 371285200104725150]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 88030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 88000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486096218822755, 362486213334818939⟩, ⟨(-96175536776275549), (-89212868901978835)⟩, true⟩

def words04 : List Nat := [371285200201420246, 371285200204487132, 371285200133206284, 371285200141028067, 371285200186825351, 371285200189952858, 371285200152585826, 371285200117122692, 371285200124400025, 371285200139410574]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 88040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 88000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk880A
