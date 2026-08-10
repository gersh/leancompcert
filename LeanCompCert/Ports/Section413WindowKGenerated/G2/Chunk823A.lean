import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk823A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360574391813001553, 360574436027713668⟩, ⟨649371340712288132, 651828869405658892⟩, true⟩

def state01 : KState := ⟨⟨360613831392511019, 360613875618355152⟩, ⟨(-2596690304863461072), (-2594231859950784828)⟩, true⟩

def words00 : List Nat := [360582356140155334, 360582356324961046, 360582356548666386, 360582356772587766, 360582356865584312, 360582356961980459, 360582357205691748, 360582357449746389, 360582357795970757, 360582358180103269]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598382452393160, 360598426689489191⟩, ⟨(-1325037855911251044), (-1322578484800013820)⟩, true⟩

def words01 : List Nat := [360582358490047284, 360582358800112428, 360582359034937645, 360582359375262323, 360582359651078120, 360582359927085254, 360582360109052898, 360582360183870061, 360582360379995122, 360582360576531380]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580972872634123, 360581017120833591⟩, ⟨108213056655903733, 110673341859052633⟩, true⟩

def words02 : List Nat := [360582360892271497, 360582361061066256, 360582361155669264, 360582361250395770, 360582361266392725, 360582361356519637, 360582361396920870, 360582361437529002, 360582361438585270, 360582361385887145]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360606262598584535, 360606306857917443⟩, ⟨(-1974086904187329967), (-1971625702312411183)⟩, true⟩

def words03 : List Nat := [360582361370516907, 360582361341185303, 360582361407448089, 360582361507832068, 360582361508927833, 360582361463900952, 360582361488247835, 360582361632913441, 360582361924676594, 360582362216702102]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360616740441814122, 360616784712418978⟩, ⟨(-2837009839943330020), (-2834547709884459126)⟩, true⟩

def words04 : List Nat := [360582362395027904, 360582362530851942, 360582362771241083, 360582363011971438, 360582363188282450, 360582363403370119, 360582363544374130, 360582363685527267, 360582363973839070, 360582364393177142]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk823A
