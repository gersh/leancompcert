import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk973A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk973B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk973A

def state06 : KState := ⟨⟨360556783579207924, 360556846267683237⟩, ⟨2483003931138228091, 2487125146018908617⟩, true⟩

def words05 : List Nat := [360582392590636182, 360582392686547039, 360582392715372480, 360582392716785769, 360582392640355648, 360582392537587447, 360582392434380840, 360582392362547710, 360582392185405871, 360582391924482939]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 97350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 97300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360573482654718688, 360573545356551516⟩, ⟨857011290488895025, 861133805922776259⟩, true⟩

def words06 : List Nat := [360582391663252772, 360582391391228762, 360582391174103490, 360582390952812627, 360582390731416355, 360582390420734372, 360582390032429356, 360582389749982468, 360582389467126209, 360582389290062072]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 97360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 97300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360570600996767521, 360570663712066957⟩, ⟨1137612541459792836, 1141736368204231308⟩, true⟩

def words07 : List Nat := [360582389200507027, 360582389049876652, 360582388898968785, 360582388859749207, 360582388860936659, 360582388801893652, 360582388742715747, 360582388602328617, 360582388377648631, 360582388258875380]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 97370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 97300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582778703584301, 360582841432191901⟩, ⟨(-48307226099529160), (-44182103338868196)⟩, true⟩

def words08 : List Nat := [360582388139619365, 360582388126055033, 360582388119183892, 360582388021009821, 360582387922581144, 360582387797795525, 360582387756533424, 360582387789445400, 360582387790717974, 360582387775248869]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 97380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 97300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360605451591544088, 360605514333522656⟩, ⟨(-2256604712313572654), (-2252478287289413532)⟩, true⟩

def words09 : List Nat := [360582387778682177, 360582387782510781, 360582387814634786, 360582387875503942, 360582387876808475, 360582387843311142, 360582387879997970, 360582388033033288, 360582388271612601, 360582388510509654]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 97390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 97300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 97300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk973B
