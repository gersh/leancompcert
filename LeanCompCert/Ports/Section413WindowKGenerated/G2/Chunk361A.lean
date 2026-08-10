import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk361A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360529438137241241, 360529446097623857⟩, ⟨1896430079790261520, 1896624348094799380⟩, true⟩

def state01 : KState := ⟨⟨360627448585894022, 360627456550857605⟩, ⟨(-1642345588774633544), (-1642151155074807732)⟩, true⟩

def words00 : List Nat := [360581982713294587, 360581981485520280, 360581980856557971, 360581980785040925, 360581980713490379, 360581979976190164, 360581979320105903, 360581979375292157, 360581980196018518, 360581981455870626]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 36100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 36100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360571825643771980, 360571833613363951⟩, ⟨366466269757772362, 366660870611404596⟩, true⟩

def words01 : List Nat := [360581982329398479, 360581983202931331, 360581983596035943, 360581984467961764, 360581985004005758, 360581985540099003, 360581985692368017, 360581985692853562, 360581985080743342, 360581984800257955]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 36110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 36100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360526962891563741, 360526970865726076⟩, ⟨1987114733166888840, 1987309499125225120⟩, true⟩

def words02 : List Nat := [360581984680295904, 360581984680781495, 360581984077639679, 360581983088727653, 360581982099789523, 360581980667950544, 360581979665744059, 360581978332416277, 360581976999109298, 360581975280315759]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 36120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 36100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360615376761441710, 360615384740187236⟩, ⟨(-1207757266294699166), (-1207562334723314784)⟩, true⟩

def words03 : List Nat := [360581973758347848, 360581973001299588, 360581972244151720, 360581971839344407, 360581971734602980, 360581970891710287, 360581970048771346, 360581970357742401, 360581971282716973, 360581972207752514]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 36130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 36100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360628486720685346, 360628494704062355⟩, ⟨(-1681851274765814500), (-1681656175789813978)⟩, true⟩

def words04 : List Nat := [360581972546858991, 360581972637367375, 360581973237543818, 360581973837834089, 360581974244232134, 360581974829402333, 360581975029236840, 360581975229121754, 360581975860470875, 360581977147817997]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 36140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 36100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk361A
