import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk170A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360735876642359200, 360735878295214164⟩, ⟨(-2598239809709952214), (-2598220788460130916)⟩, true⟩

def state01 : KState := ⟨⟨360672211851581057, 360672213506487473⟩, ⟨(-1516293386884184955), (-1516274330749936899)⟩, true⟩

def words00 : List Nat := [360583058022663974, 360583061853745832, 360583065392976121, 360583068931850799, 360583070761122198, 360583072121989300, 360583072122180824, 360583071742213822, 360583073333940447, 360583078574340631]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 17000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 17000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360504837964633304, 360504839621564307⟩, ⟨1332062530998997290, 1332081621581654080⟩, true⟩

def words01 : List Nat := [360583087255602927, 360583095935885694, 360583102591871838, 360583107132907101, 360583109916249649, 360583112699321595, 360583112699501193, 360583112318184044, 360583109885256944, 360583105286757119]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 17010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 17000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360664056055502279, 360664057714465249⟩, ⟨(-1378717317536109108), (-1378698192359251798)⟩, true⟩

def words02 : List Nat := [360583100688748825, 360583100081303248, 360583102354540150, 360583104627554994, 360583104627753622, 360583103819124687, 360583099599662861, 360583098816609809, 360583100685917377, 360583105439651131]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 17020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 17000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360684823055588967, 360684824716604044⟩, ⟨(-1732486155822398416), (-1732466995687689360)⟩, true⟩

def words03 : List Nat := [360583107506481226, 360583109573088948, 360583115073914476, 360583123089128510, 360583130204809843, 360583137319690945, 360583142670671942, 360583148150910180, 360583154118020311, 360583160084499843]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 17030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 17000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360699833475137939, 360699835138182409⟩, ⟨(-1988607535319669241), (-1988588340593814639)⟩, true⟩

def words04 : List Nat := [360583169481183252, 360583175471027435, 360583178776475760, 360583182081558317, 360583183017110200, 360583185722693971, 360583191856897307, 360583197990422161, 360583202390708544, 360583209231162656]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 17040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 17000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk170A
