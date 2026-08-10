import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk774A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584721002389789, 360584759921932498⟩, ⟨(-201558277963876908), (-199523710124129282)⟩, true⟩

def state01 : KState := ⟨⟨360573474517640808, 360573513447589845⟩, ⟨668958950836104202, 670994324176298440⟩, true⟩

def words00 : List Nat := [360582182146738452, 360582182147848385, 360582182130208692, 360582182029334879, 360582181928283182, 360582181765337078, 360582181747253231, 360582181702555891, 360582181657749351, 360582181505000727]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 77400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 77400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598445032367607, 360598483972763735⟩, ⟨(-1264218001911799199), (-1262181819812222065)⟩, true⟩

def words01 : List Nat := [360582181424420759, 360582181456138653, 360582181483623922, 360582181484728783, 360582181345929763, 360582181065155980, 360582180784177952, 360582180714143609, 360582180925619037, 360582181137359747]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 77410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 77400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360572733911225820, 360572772862139020⟩, ⟨726386280704299984, 728423277087652458⟩, true⟩

def words02 : List Nat := [360582181258531430, 360582181259636452, 360582181300642883, 360582181388160370, 360582181389088435, 360582181390121652, 360582181224696704, 360582180930753392, 360582180636606958, 360582180369269172]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 77420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 77400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360566790054271100, 360566829015587289⟩, ⟨1186715678643005948, 1188753480582862298⟩, true⟩

def words03 : List Nat := [360582180293661709, 360582180339760021, 360582180340745055, 360582180293053326, 360582180249326912, 360582180106521420, 360582179963382722, 360582179957303361, 360582179851617959, 360582179654541097]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 77430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 77400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360571981962534495, 360572020934293932⟩, ⟨784563506755901744, 786602117472904344⟩, true⟩

def words04 : List Nat := [360582179457232903, 360582179133448704, 360582178892828327, 360582178759715168, 360582178626526892, 360582178352760102, 360582177912529207, 360582177639075322, 360582177365283384, 360582177191459496]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 77440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 77400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk774A
