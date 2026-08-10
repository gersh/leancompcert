import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk577A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360567460187516974, 360567481317395994⟩, ⟨831819028859042097, 832642727707371149⟩, true⟩

def state01 : KState := ⟨⟨360598198177652704, 360598219315142627⟩, ⟨(-941977727926178829), (-941153589891587365)⟩, true⟩

def words00 : List Nat := [360581911617839883, 360581911360400976, 360581911366788196, 360581911436191874, 360581911436934200, 360581911252159868, 360581911144759908, 360581910992367277, 360581910986637533, 360581911270057781]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 57700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 57700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584834220912990, 360584855366065539⟩, ⟨(-170659579510824387), (-169834999228111941)⟩, true⟩

def words01 : List Nat := [360581911402012468, 360581911534050538, 360581911966101235, 360581912548519580, 360581912832403598, 360581913116395954, 360581913167547048, 360581913168352403, 360581912970838337, 360581913022737667]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 57710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 57700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360614841230259813, 360614862383006954⟩, ⟨(-1902792228519161045), (-1901967209839094765)⟩, true⟩

def words02 : List Nat := [360581913325987293, 360581913764277219, 360581914025253084, 360581914286307782, 360581914469944328, 360581914803674177, 360581915437184086, 360581916070832104, 360581916475194067, 360581917046708621]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 57720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 57700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360627656894207222, 360627678054553412⟩, ⟨(-2642689724294250530), (-2641864266882414202)⟩, true⟩

def words03 : List Nat := [360581917918032275, 360581918789564468, 360581919748938307, 360581920408995619, 360581920811861570, 360581921214783457, 360581921917474090, 360581922770379512, 360581923563472241, 360581924356715093]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 57730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 57700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595035134084403, 360595056302117244⟩, ⟨(-759111111190432685), (-758285209915808801)⟩, true⟩

def words04 : List Nat := [360581924967082150, 360581925278157751, 360581925526705482, 360581925775477805, 360581925947514494, 360581926034228385, 360581926034946180, 360581925970440439, 360581925905784718, 360581926049655542]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 57740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 57700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk577A
