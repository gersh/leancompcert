import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk263A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360630389911256342, 360630394024443283⟩, ⟨(-1250932295832130434), (-1250859121052434246)⟩, true⟩

def state01 : KState := ⟨⟨360618962673862901, 360618966790330494⟩, ⟨(-950792512308999134), (-950719251231266308)⟩, true⟩

def words00 : List Nat := [360582835350674973, 360582835351019858, 360582834623393812, 360582834635526617, 360582834635815463, 360582834275963352, 360582833963430154, 360582832664808173, 360582831508628864, 360582832882412465]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 26300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 26300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360556794517235270, 360556798636958803⟩, ⟨685314910493880456, 685388257251244608⟩, true⟩

def words01 : List Nat := [360582835320832692, 360582837759137719, 360582839079287131, 360582839571011568, 360582839571301089, 360582839371338728, 360582840411361137, 360582840411706203, 360582840213298747, 360582839224240386]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 26310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 26300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592399899276840, 360592404022255561⟩, ⟨(-251886379994027875), (-251812947543951111)⟩, true⟩

def words02 : List Nat := [360582838686044662, 360582840064849753, 360582841660931057, 360582843256955119, 360582843618375327, 360582843618720501, 360582842541874141, 360582841426767698, 360582840311645271, 360582840657873504]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 26320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 26300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603493264694876, 360603497390963419⟩, ⟨(-544147340220131821), (-544073821133290013)⟩, true⟩

def words03 : List Nat := [360582840658181273, 360582840114308730, 360582839570412122, 360582840780708686, 360582841248563298, 360582841716438174, 360582841716745998, 360582841457979394, 360582841588704631, 360582842373267307]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 26330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 26300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573736329574536, 360573740459099064⟩, ⟨239450822115528123, 239524426981321683⟩, true⟩

def words04 : List Nat := [360582842696941316, 360582842697286759, 360582841584675538, 360582839756671920, 360582837928752658, 360582835159379092, 360582833115392601, 360582832509007538, 360582831902625096, 360582830570179950]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 26340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 26300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk263A
