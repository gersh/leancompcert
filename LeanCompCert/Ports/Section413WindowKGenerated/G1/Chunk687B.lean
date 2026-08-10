import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk687A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk687B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk687A

def state06 : KState := ⟨⟨362483663982287644, 362483734050895837⟩, ⟨113666517808789041, 116920433050154569⟩, true⟩

def words05 : List Nat := [371285434582818865, 371285434473117090, 371285434446469872, 371285434457411510, 371285434531941072, 371285434607347777, 371285434664615086, 371285434666967798, 371285434486176674, 371285434464407329]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 68750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 68700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468127588353541, 362468197677933610⟩, ⟨1181971420633365235, 1185226778008814143⟩, true⟩

def words06 : List Nat := [371285434441315504, 371285434418584334, 371285434113546715, 371285433809593442, 371285433504774272, 371285433216807487, 371285432834814892, 371285432665003805, 371285432494343754, 371285432326443263]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 68760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 68700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493867560253007, 362493937671037559⟩, ⟨(-588292743824303759), (-585035928107631799)⟩, true⟩

def words07 : List Nat := [371285432077428787, 371285432040750522, 371285432140507846, 371285432142859431, 371285432021954352, 371285431848469324, 371285431709048221, 371285431711663524, 371285431766578881, 371285431892870513]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 68770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 68700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473430282753941, 362473500414772507⟩, ⟨817470314130097214, 820728590431902598⟩, true⟩

def words08 : List Nat := [371285431995422084, 371285431997821328, 371285431962433397, 371285431965684481, 371285432032248919, 371285432034600752, 371285431843381895, 371285431652507530, 371285431460729860, 371285431343547502]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 68780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 68700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474061532294233, 362474131685540848⟩, ⟨774121100955776045, 777380837635295273⟩, true⟩

def words09 : List Nat := [371285431209277474, 371285431249421836, 371285431270579443, 371285431272948585, 371285431138797183, 371285431070401097, 371285431115050003, 371285431117403327, 371285430987175377, 371285430825622757]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 68790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 68700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 68700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk687B
