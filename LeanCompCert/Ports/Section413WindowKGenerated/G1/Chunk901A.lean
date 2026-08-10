import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk901A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474577026050037, 362474699876812208⟩, ⟨930580402337442027, 938053919195999165⟩, true⟩

def state01 : KState := ⟨⟨362477112989727242, 362477235868602349⟩, ⟨702078192492064239, 709554242474472571⟩, true⟩

def words00 : List Nat := [371285111016672719, 371285110967435107, 371285110855454574, 371285110798657242, 371285110740794315, 371285110664006965, 371285110422060455, 371285110304869413, 371285110186049258, 371285110180470893]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 90100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 90100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482601932587737, 362482724840188466⟩, ⟨207431180807857356, 214909819398098618⟩, true⟩

def words01 : List Nat := [371285110095478013, 371285109986358163, 371285109875892084, 371285109868880839, 371285109808701695, 371285109777205510, 371285109744696054, 371285109701909251, 371285109569997814, 371285109547460971]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 90110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 90100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475417885321406, 362475540820904131⟩, ⟨854906021428655578, 862387181903040096⟩, true⟩

def words02 : List Nat := [371285109619746876, 371285109622891176, 371285109557779811, 371285109471062866, 371285109383213044, 371285109298089123, 371285109150926096, 371285109128151296, 371285109104283437, 371285109079884527]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 90120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 90100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493495769811392, 362493618733815516⟩, ⟨(-774506746348021952), (-767023024110795160)⟩, true⟩

def words03 : List Nat := [371285108987296403, 371285109002535095, 371285109128866898, 371285109173844815, 371285109197680852, 371285109222508456, 371285109334499257, 371285109392292016, 371285109488863597, 371285109586766884]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 90130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 90100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493609837169339, 362493732829553446⟩, ⟨(-784826279082886856), (-777339998531001294)⟩, true⟩

def words04 : List Nat := [371285109683352586, 371285109686512862, 371285109754432204, 371285109847693944, 371285109937529981, 371285109944141945, 371285109950189209, 371285109957273044, 371285110086098706, 371285110185339505]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 90140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 90100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk901A
