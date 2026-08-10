import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk994A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584013711171899, 360584079158883843⟩, ⟨(-168400203258189923), (-164007524541852173)⟩, true⟩

def state01 : KState := ⟨⟨360601052982808963, 360601118444145839⟩, ⟨(-1862156615032984842), (-1857762581928865700)⟩, true⟩

def words00 : List Nat := [360582429319308982, 360582429489161652, 360582429739229811, 360582429989570129, 360582430152220539, 360582430267748951, 360582430330767552, 360582430394184624, 360582430558312624, 360582430747795045]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360604459892097215, 360604525367201987⟩, ⟨(-2200865586949814449), (-2196470185112034609)⟩, true⟩

def words01 : List Nat := [360582430872984554, 360582430998324679, 360582431201746374, 360582431484745005, 360582431720607559, 360582431956705706, 360582432136964571, 360582432301839384, 360582432525227818, 360582432749092010]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589447686394928, 360589513175129335⟩, ⟨(-708322546529762653), (-703925789566981785)⟩, true⟩

def words02 : List Nat := [360582432969019866, 360582433088328956, 360582433156757860, 360582433225338206, 360582433235549430, 360582433305585007, 360582433419630033, 360582433533973391, 360582433561950064, 360582433634648329]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603913318816276, 360603978821190641⟩, ⟨(-2146735746714090264), (-2142337633460850420)⟩, true⟩

def words03 : List Nat := [360582433808111586, 360582433982011159, 360582434190076763, 360582434322843013, 360582434359141800, 360582434395529250, 360582434461821021, 360582434578996613, 360582434796820864, 360582435014979312]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360603143092415398, 360603208608588298⟩, ⟨(-2070180829506334968), (-2065781344063562012)⟩, true⟩

def words04 : List Nat := [360582435167772330, 360582435322934368, 360582435563006467, 360582435803498640, 360582436018020545, 360582436189001188, 360582436309191382, 360582436429538330, 360582436547139361, 360582436757686210]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk994A
