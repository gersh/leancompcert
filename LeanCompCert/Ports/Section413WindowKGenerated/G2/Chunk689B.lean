import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk689A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk689B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk689A

def state06 : KState := ⟨⟨360598247048808501, 360598277661896664⟩, ⟨(-1070017489168591512), (-1068591511618287050)⟩, true⟩

def words05 : List Nat := [360582780307967080, 360582780527738502, 360582780892888330, 360582781161610792, 360582781250972828, 360582781340408052, 360582781425543022, 360582781618798773, 360582781844303297, 360582782070016931]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 68950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 68900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588445659935822, 360588476282314369⟩, ⟨(-394132820212845461), (-392706201953717719)⟩, true⟩

def words06 : List Nat := [360582782180043099, 360582782243567694, 360582782516738589, 360582782790206301, 360582782948301907, 360582782949277335, 360582782897448084, 360582782711860780, 360582782526093818, 360582782495042129]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 68960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 68900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560777733596752, 360560808365168561⟩, ⟨1514212750389211465, 1515640002754332463⟩, true⟩

def words07 : List Nat := [360582782521237275, 360582782547604844, 360582782548474213, 360582782460760308, 360582782162950807, 360582781762827844, 360582781362421530, 360582781061237414, 360582780848577899, 360582780531053663]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 68970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 68900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584535651728620, 360584566292502546⟩, ⟨(-124737215420780787), (-123309328247476605)⟩, true⟩

def words08 : List Nat := [360582780213323000, 360582779928466575, 360582779749042144, 360582779728808507, 360582779708524890, 360582779491933734, 360582779206203847, 360582779087244730, 360582778968004655, 360582778967659488]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 68980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 68900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569233788524218, 360569264438604422⟩, ⟨931066888273182597, 932495417532300869⟩, true⟩

def words09 : List Nat := [360582778968534048, 360582778837712074, 360582778784499628, 360582778968513786, 360582779099580083, 360582779230801910, 360582779249686486, 360582779250662401, 360582779059693594, 360582778864945470]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 68990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 68900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 68900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk689B
