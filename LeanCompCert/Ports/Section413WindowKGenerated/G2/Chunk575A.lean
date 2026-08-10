import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk575A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360613148525669658, 360613169503458724⟩, ⟨(-1796219384469738176), (-1795404445999809154)⟩, true⟩

def state01 : KState := ⟨⟨360591692103444711, 360591713088870390⟩, ⟨(-562512544572916736), (-561697166960401974)⟩, true⟩

def words00 : List Nat := [360581946014717134, 360581946106474438, 360581946500477779, 360581946894702689, 360581947046692215, 360581947047494355, 360581946897839088, 360581946566803122, 360581946235619703, 360581946310915557]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 57500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 57500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360549854814088522, 360549875807078721⟩, ⟨1843832094187544193, 1844647906873620503⟩, true⟩

def words01 : List Nat := [360581946568917553, 360581946827080314, 360581946900625736, 360581946901428027, 360581946753383037, 360581946528639602, 360581946322981851, 360581946323784154, 360581946042289878, 360581945485570961]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 57510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 57500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360601927109916976, 360601948110481956⟩, ⟨(-1151715749123801068), (-1150899500700210890)⟩, true⟩

def words02 : List Nat := [360581944928689764, 360581944584252995, 360581944390690683, 360581944190022205, 360581943989302598, 360581943514822108, 360581943059978926, 360581942907536381, 360581942903654201, 360581943252219451]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 57520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 57500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360593678477427222, 360593699485640410⟩, ⟨(-677181826568393561), (-676365138106070773)⟩, true⟩

def words03 : List Nat := [360581943426800180, 360581943601464101, 360581943767275629, 360581944127515942, 360581944340132063, 360581944552872710, 360581944612167398, 360581944612973758, 360581944789921281, 360581944995136143]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 57530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 57500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360566618567929582, 360566639583693684⟩, ⟨879923016620541396, 880740139601167020⟩, true⟩

def words04 : List Nat := [360581945245151357, 360581945245953977, 360581945194711064, 360581944991177427, 360581944787521773, 360581944409920775, 360581944225819485, 360581944033252240, 360581943840604125, 360581943495763210]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 57540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 57500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk575A
