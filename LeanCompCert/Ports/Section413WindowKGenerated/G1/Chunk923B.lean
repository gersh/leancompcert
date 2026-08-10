import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk923A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk923B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk923A

def state06 : KState := ⟨⟨362491939668917881, 362492069007369288⟩, ⟨(-651299029876556042), (-643233607573506094)⟩, true⟩

def words05 : List Nat := [371285104709067878, 371285104671490006, 371285104707851955, 371285104711081714, 371285104649123746, 371285104566976749, 371285104515065507, 371285104518720510, 371285104586132523, 371285104665194848]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 92350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 92300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478046578975043, 362478175946530468⟩, ⟨631895721954161079, 639963832454677031⟩, true⟩

def words06 : List Nat := [371285104729354101, 371285104732583515, 371285104663022713, 371285104689564806, 371285104707060323, 371285104710289872, 371285104571732333, 371285104412999464, 371285104252907418, 371285104211469893]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 92360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 92300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480754166490722, 362480883563151747⟩, ⟨381797558334766366, 389868357466816890⟩, true⟩

def words07 : List Nat := [371285104165897788, 371285104196676053, 371285104216583827, 371285104219813678, 371285104083414832, 371285103983281681, 371285103894484938, 371285103897768617, 371285103873230109, 371285103831147708]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 92370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 92300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493902762371993, 362494032187909257⟩, ⟨(-832879048875455336), (-824805582004470788)⟩, true⟩

def words08 : List Nat := [371285103859099367, 371285103881539237, 371285104019731746, 371285104159282393, 371285104277961413, 371285104299872446, 371285104437803629, 371285104577372783, 371285104751054346, 371285104851025746]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 92380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 92300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489360366636136, 362489489821714334⟩, ⟨(-413188157756967330), (-405111961464603156)⟩, true⟩

def words09 : List Nat := [371285104938990213, 371285105028057971, 371285105153455288, 371285105234607684, 371285105325145972, 371285105416884967, 371285105505750408, 371285105508981425, 371285105488975284, 371285105540575985]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 92390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 92300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 92300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk923B
