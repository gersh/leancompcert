import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk665A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360574464705885638, 360574493091746823⟩, ⟨558746577705688630, 560021687432320802⟩, true⟩

def state01 : KState := ⟨⟨360577232423277150, 360577260818076921⟩, ⟨374545712657476758, 375821416844297216⟩, true⟩

def words00 : List Nat := [360582914344714199, 360582914101479976, 360582913728545849, 360582913523335417, 360582913317880105, 360582913025878852, 360582912699408289, 360582912197160597, 360582911694743952, 360582911418239969]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360558495559045473, 360558523962671826⟩, ⟨1620925890309065629, 1622202181596823539⟩, true⟩

def words01 : List Nat := [360582911432173816, 360582911531241711, 360582911532077596, 360582911518377246, 360582911510908699, 360582911409183913, 360582911307190619, 360582911240167881, 360582911011740438, 360582910646099319]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587393984615027, 360587422397116003⟩, ⟨(-301637415528165025), (-300360533857089583)⟩, true⟩

def words02 : List Nat := [360582910280276006, 360582909742114762, 360582909316860512, 360582909117269108, 360582908917611788, 360582908526568828, 360582908151023252, 360582907937018604, 360582907733077506, 360582907801906897]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583871620520249, 360583900041954334⟩, ⟨(-67253660730639686), (-65976184694569826)⟩, true⟩

def words03 : List Nat := [360582907802743166, 360582907731050291, 360582907811967412, 360582908110906661, 360582908253714566, 360582908396657571, 360582908425580931, 360582908498546218, 360582908514212741, 360582908530184229]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360598108100745025, 360598136531030074⟩, ⟨(-1014590245312362902), (-1013312180288997788)⟩, true⟩

def words04 : List Nat := [360582908771221639, 360582909053143881, 360582909188952429, 360582909324858924, 360582909404074872, 360582909597089142, 360582909856898980, 360582910116877226, 360582910201270976, 360582910431042261]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk665A
