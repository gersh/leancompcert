import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk806A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk806B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk806A

def state06 : KState := ⟨⟨362493826587701594, 362493924208012896⟩, ⟨(-712824746036223148), (-707507772625539766)⟩, true⟩

def words05 : List Nat := [371285153036096202, 371285152947167393, 371285152888803648, 371285152891642858, 371285152798441617, 371285152695151569, 371285152637930877, 371285152641034121, 371285152722475140, 371285152834330131]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 80650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 80600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478477460741126, 362478575106241925⟩, ⟨525249825502996028, 530568830829022430⟩, true⟩

def words06 : List Nat := [371285152907198605, 371285152909990841, 371285152809608556, 371285152789513163, 371285152768028364, 371285152756482426, 371285152562328693, 371285152368720264, 371285152173952172, 371285152134019650]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 80660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 80600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486759278478036, 362486856949127828⟩, ⟨(-142844637631538054), (-137523603409254700)⟩, true⟩

def words07 : List Nat := [371285152126390453, 371285152201463941, 371285152275680795, 371285152278496509, 371285152249641252, 371285152231069873, 371285152342643122, 371285152366438983, 371285152389652706, 371285152413940991]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 80670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 80600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362497068797552374, 362497166493208918⟩, ⟨(-974595445966264364), (-969272394072488826)⟩, true⟩

def words08 : List Nat := [371285152590454042, 371285152725305022, 371285153012399208, 371285153300601551, 371285153537447199, 371285153570234899, 371285153755601127, 371285153942449684, 371285154191470898, 371285154343228469]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 80680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 80600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490492550478455, 362490590271537885⟩, ⟨(-443892379451446518), (-438567277670332158)⟩, true⟩

def words09 : List Nat := [371285154491848037, 371285154641371514, 371285154879284965, 371285155042000464, 371285155250898639, 371285155460960475, 371285155655301855, 371285155660107493, 371285155729350040, 371285155800122781]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 80690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 80600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 80600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk806B
