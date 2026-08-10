import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk370A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk370B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk370A

def state06 : KState := ⟨⟨360528399628403738, 360528408035852295⟩, ⟨1970348676957597873, 1970559299917312931⟩, true⟩

def words05 : List Nat := [360581590155901769, 360581589644932032, 360581589133940013, 360581588151571109, 360581586695246764, 360581585052015585, 360581583408727021, 360581582493300969, 360581581604505649, 360581580170226751]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 37050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 37000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588582598612111, 360588591010770472⟩, ⟨(-260316139910657566), (-260105342382313702)⟩, true⟩

def words06 : List Nat := [360581578735910993, 360581578029403300, 360581577809989037, 360581577806447781, 360581577802875434, 360581577096686940, 360581575957217987, 360581575338230177, 360581574719130497, 360581574600574300]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 37060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 37000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560108756157062, 360560117173078606⟩, ⟨795477676068764583, 795688650191470975⟩, true⟩

def words07 : List Nat := [360581574601023596, 360581574418134888, 360581574616426078, 360581575485671443, 360581576162662168, 360581576839700811, 360581577009039464, 360581577009538884, 360581576452694850, 360581575874540081]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 37070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 37000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360551830666709503, 360551839088332288⟩, ⟨1102333262724422598, 1102544411192940616⟩, true⟩

def words08 : List Nat := [360581575296248632, 360581574823782028, 360581573625226327, 360581572001025636, 360581570376830990, 360581568566261444, 360581567315354556, 360581566790991205, 360581566266606648, 360581565278981869]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 37080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 37000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587501301597833, 360587509727942470⟩, ⟨(-220971498469911142), (-220760174845042258)⟩, true⟩

def words09 : List Nat := [360581564477946745, 360581564059725366, 360581563641383727, 360581563191036709, 360581562505573404, 360581561206750715, 360581559907902443, 360581559335289710, 360581559318390296, 360581559479301058]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 37090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 37000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 37000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk370B
