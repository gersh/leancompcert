import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk985A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk985B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk985A

def state06 : KState := ⟨⟨360563119741755757, 360563184045987268⟩, ⟨1891967680308121130, 1896247176656981930⟩, true⟩

def words05 : List Nat := [360582423985026763, 360582424123699550, 360582424177990149, 360582424179421896, 360582424130966357, 360582424027665982, 360582423923946717, 360582423893634045, 360582423760544083, 360582423566854324]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 98550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 98500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593074377228432, 360593138694959591⟩, ⟨(-1060484741785662055), (-1056203914842778829)⟩, true⟩

def words06 : List Nat := [360582423372807474, 360582423282058442, 360582423304065688, 360582423367357842, 360582423368678382, 360582423344654694, 360582423345504312, 360582423344361996, 360582423426003841, 360582423536192380]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 98560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 98500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592707097843698, 360592771429213047⟩, ⟨(-1024276488832399649), (-1019994317507587163)⟩, true⟩

def words07 : List Nat := [360582423555776249, 360582423575509317, 360582423697812819, 360582423900449905, 360582424076739381, 360582424253257930, 360582424377078992, 360582424452743477, 360582424558866778, 360582424665460320]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 98570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 98500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591077809609330, 360591142154475925⟩, ⟨(-863683507703625557), (-859400005751225787)⟩, true⟩

def words08 : List Nat := [360582424769204275, 360582424857498665, 360582424873811013, 360582424890275955, 360582424891474468, 360582424922908512, 360582425051448521, 360582425180285923, 360582425244526236, 360582425334423880]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 98580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 98500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360599103603472859, 360599167961857498⟩, ⟨(-1655038598914338113), (-1650753764151971491)⟩, true⟩

def words09 : List Nat := [360582425469240102, 360582425604479536, 360582425755084112, 360582425803400591, 360582425804757236, 360582425755947701, 360582425759416671, 360582425864825421, 360582426035781782, 360582426207066452]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 98590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 98500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 98500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk985B
