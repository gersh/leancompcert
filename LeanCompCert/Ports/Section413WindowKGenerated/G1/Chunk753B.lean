import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk753A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk753B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk753A

def state06 : KState := ⟨⟨362480441385861707, 362480526154007854⟩, ⟨349306060369340992, 353620022567741026⟩, true⟩

def words05 : List Nat := [371285219140884037, 371285219008210182, 371285218914910382, 371285218917774455, 371285218892260780, 371285218875854578, 371285218858616601, 371285218843487261, 371285218623088852, 371285218564073775]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 75350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 75300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469830946351558, 362469915737619574⟩, ⟨1148973429830598345, 1153289134613623283⟩, true⟩

def words06 : List Nat := [371285218503594118, 371285218465506818, 371285218282200682, 371285218099816827, 371285217916467619, 371285217787802715, 371285217582821321, 371285217554805303, 371285217525926184, 371285217437694055]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 75360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 75300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489956273267117, 362490041087971879⟩, ⟨(-367996926911689602), (-363679455582132986)⟩, true⟩

def words07 : List Nat := [371285217236439519, 371285217120649844, 371285217014878050, 371285217017484790, 371285216867349511, 371285216682535090, 371285216496586218, 371285216487587955, 371285216470388312, 371285216537281624]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 75370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 75300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470025814051246, 362470110652183462⟩, ⟨1134386922411407132, 1138706159822492576⟩, true⟩

def words08 : List Nat := [371285216603312451, 371285216605906979, 371285216437307448, 371285216283878778, 371285216129115956, 371285216028729918, 371285215693236160, 371285215356865066, 371285215019469693, 371285214859105103]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 75380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 75300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362461727236227785, 362461812097749456⟩, ⟨1760147054769811600, 1764468055626407336⟩, true⟩

def words09 : List Nat := [371285214660520295, 371285214638809838, 371285214616196245, 371285214593493465, 371285214447709109, 371285214317915565, 371285214186838463, 371285214130072883, 371285213838256260, 371285213530847950]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 75390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 75300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 75300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk753B
