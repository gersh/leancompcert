import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk334A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk334B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk334A

def state06 : KState := ⟨⟨360525681889568073, 360525688685514939⟩, ⟨1858091559443893996, 1858245307867062994⟩, true⟩

def words05 : List Nat := [360581230978229094, 360581231379823094, 360581231380232437, 360581231044881470, 360581230171683373, 360581229072098479, 360581227972447136, 360581227764394416, 360581226666091850, 360581225006730333]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 33450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 33400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595043617331087, 360595050417496968⟩, ⟨(-463000595444862490), (-462846705832710598)⟩, true⟩

def words06 : List Nat := [360581223347359148, 360581222579553700, 360581223205371514, 360581223862326226, 360581223862739120, 360581223632768426, 360581222953181420, 360581222243177878, 360581221713543521, 360581222127161074]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 33460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 33400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577007348428635, 360577014152858249⟩, ⟨140653817460441261, 140807849800682033⟩, true⟩

def words07 : List Nat := [360581222127563273, 360581222091876767, 360581222056110350, 360581222063050403, 360581222063427038, 360581221866060595, 360581221668657229, 360581221023964221, 360581220008246681, 360581219883139035]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 33470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 33400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360562213667555680, 360562220476204021⟩, ⟨635803133143501177, 635957306748143853⟩, true⟩

def words08 : List Nat := [360581219757891720, 360581219606339080, 360581218565924399, 360581217078587578, 360581215591263986, 360581213673181477, 360581212202976807, 360581211622936017, 360581211042874436, 360581209944903578]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 33480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 33400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588297465378691, 360588304278249510⟩, ⟨(-237883553034211325), (-237729237998143719)⟩, true⟩

def words09 : List Nat := [360581209488595091, 360581209599412989, 360581210599755409, 360581210711828030, 360581210712250954, 360581209885852729, 360581209059419261, 360581208138635838, 360581207882621411, 360581208094911755]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 33490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 33400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 33400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk334B
