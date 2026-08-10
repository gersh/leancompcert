import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk604A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491987954388276, 362492041472345064⟩, ⟨(-413151388772736511), (-410967920800739279)⟩, true⟩

def state01 : KState := ⟨⟨362488463229671472, 362488516765942901⟩, ⟨(-200272963355920920), (-198088389083365450)⟩, true⟩

def words00 : List Nat := [371285237627909636, 371285237639813363, 371285237762952405, 371285237886876622, 371285237968625473, 371285237970670732, 371285237686790060, 371285237606281315, 371285237697589992, 371285237754023162]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 60400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 60400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494336806960728, 362494390361839328⟩, ⟨(-555099643091666106), (-552913944666092914)⟩, true⟩

def words01 : List Nat := [371285237807360258, 371285237861375227, 371285238188883224, 371285238380818561, 371285238640296860, 371285238900579136, 371285239105977244, 371285239108028518, 371285239185131238, 371285239339104417]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 60410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 60400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479727378345522, 362479780951441424⟩, ⟨327659641967623213, 329846441176900101⟩, true⟩

def words02 : List Nat := [371285239617386821, 371285239619432845, 371285239532612525, 371285239395273257, 371285239257088619, 371285239204909178, 371285239100654502, 371285239187146537, 371285239272030432, 371285239274148307]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 60420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 60400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362499456337442449, 362499509929079722⟩, ⟨(-864679789621840640), (-862491869863484938)⟩, true⟩

def words03 : List Nat := [371285239185237418, 371285239164044786, 371285239356342129, 371285239377146208, 371285239378748801, 371285239338039219, 371285239434099535, 371285239473016625, 371285239710517199, 371285239948936054]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 60430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 60400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485908483864332, 362485962093957122⟩, ⟨(-45833716560459441), (-43644681257905187)⟩, true⟩

def words04 : List Nat := [371285240185668054, 371285240187715423, 371285240308107051, 371285240507084669, 371285240662119448, 371285240664166316, 371285240454310341, 371285240244314836, 371285240095225696, 371285240109519183]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 60440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 60400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk604A
