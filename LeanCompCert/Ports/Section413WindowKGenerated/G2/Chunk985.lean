import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk985

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575206640486321, 360575270863415949⟩, ⟨700260588034118400, 704532073714760008⟩, true⟩

def state01 : KState := ⟨⟨360589129887020989, 360589194123449520⟩, ⟨(-671248614031870935), (-666975798640559035)⟩, true⟩

def words00 : List Nat := [360582423401849103, 360582423371049371, 360582423464442444, 360582423558132929, 360582423559474241, 360582423554819654, 360582423447152494, 360582423442896530, 360582423481437591, 360582423551649005]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 98500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 98500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360588799257943676, 360588863508027113⟩, ⟨(-638739946269720478), (-634465785667378038)⟩, true⟩

def words01 : List Nat := [360582423552946250, 360582423543724235, 360582423534267930, 360582423602048756, 360582423603252641, 360582423588781593, 360582423574144910, 360582423508062213, 360582423536990255, 360582423603989727]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 98510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 98500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360573083142774529, 360573147406324567⟩, ⟨909677039558529749, 913952526958924951⟩, true⟩

def words02 : List Nat := [360582423750731209, 360582423795034791, 360582423796323819, 360582423773024983, 360582423749515473, 360582423653132308, 360582423607697018, 360582423518048160, 360582423428244898, 360582423287040684]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 98520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 98500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592062845913390, 360592127123004241⟩, ⟨(-960488932486869775), (-956212110846738527)⟩, true⟩

def words03 : List Nat := [360582423194056631, 360582423161060978, 360582423195906144, 360582423221014354, 360582423222334590, 360582423160025120, 360582423121352252, 360582423225322647, 360582423324977122, 360582423424941032]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 98530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 98500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587595425033277, 360587659715762993⟩, ⟨(-520278305021181360), (-516000139341354152)⟩, true⟩

def words04 : List Nat := [360582423473163681, 360582423474596580, 360582423560407574, 360582423655766095, 360582423724650747, 360582423795902335, 360582423810222495, 360582423824698840, 360582423825868097, 360582423846625782]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 98540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 98500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk985
