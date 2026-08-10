import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk826A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk826B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk826A

def state06 : KState := ⟨⟨362495467363813553, 362495570078613689⟩, ⟨(-856361995551114105), (-850628983278585095)⟩, true⟩

def words05 : List Nat := [371285277989544963, 371285278182070576, 371285278373424240, 371285278497701885, 371285278654722722, 371285278813293154, 371285279116684888, 371285279252156554, 371285279378794251, 371285279506478359]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362496954692506722, 362497057432956920⟩, ⟨(-979282860011879920), (-973547727371391592)⟩, true⟩

def words06 : List Nat := [371285279765581352, 371285279964606390, 371285280218306270, 371285280473156929, 371285280679881257, 371285280692127579, 371285280800753641, 371285280910822519, 371285281117765962, 371285281263231486]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496177591107761, 362496280357691078⟩, ⟨(-915018260223099558), (-909280967028083318)⟩, true⟩

def words07 : List Nat := [371285281391899916, 371285281521564427, 371285281774462083, 371285281955637225, 371285282178405404, 371285282402258165, 371285282601097607, 371285282626404800, 371285282761365499, 371285282897972061]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484009384280903, 362484112176378850⟩, ⟨91135559944626840, 96874962821155630⟩, true⟩

def words08 : List Nat := [371285283160166296, 371285283228275848, 371285283295536603, 371285283363770876, 371285283448690159, 371285283461792479, 371285283548305714, 371285283636026701, 371285283717284792, 371285283720251400]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497087934463615, 362497190752464479⟩, ⟨(-990433733824717913), (-984692188902592335)⟩, true⟩

def words09 : List Nat := [371285283753884308, 371285283803136512, 371285283948195859, 371285283951061671, 371285283917020949, 371285283843953342, 371285283804484149, 371285283807719506, 371285283951336505, 371285284098507422]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk826B
