import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk787A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk787B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk787A

def state06 : KState := ⟨⟨360549694976082974, 360549735330595128⟩, ⟨2557571249445128335, 2559717862615704107⟩, true⟩

def words05 : List Nat := [360582237251049166, 360582237227319640, 360582237203466467, 360582237099095116, 360582236958294403, 360582236740490345, 360582236522377552, 360582236300480374, 360582235968874803, 360582235557393195]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 78750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 78700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360553820392206499, 360553860757330816⟩, ⟨2232623799268034549, 2234771248305239185⟩, true⟩

def words06 : List Nat := [360582235145662088, 360582234725946107, 360582234386558526, 360582234167660263, 360582233948659877, 360582233581032266, 360582233052329410, 360582232526060466, 360582231999463107, 360582231599635060]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 78760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 78700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360562308904037691, 360562349279898950⟩, ⟨1563862616885582916, 1566010911722291952⟩, true⟩

def words07 : List Nat := [360582231240494334, 360582230738732416, 360582230236767898, 360582229828613127, 360582229517482021, 360582229113215300, 360582228708845191, 360582228223418986, 360582227811107856, 360582227560068058]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 78770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 78700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360574009519093000, 360574049905540162⟩, ⟨642038590442419149, 644187719291979559⟩, true⟩

def words08 : List Nat := [360582227308654652, 360582227218347546, 360582227103710392, 360582226908624067, 360582226713375662, 360582226407276717, 360582226183348266, 360582226120497323, 360582226057525343, 360582225914161713]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 78780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 78700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360572911418340670, 360572951815430673⟩, ⟨728533414876451515, 730683382326891149⟩, true⟩

def words09 : List Nat := [360582225868378649, 360582225926714869, 360582225927638219, 360582225869701747, 360582225650933032, 360582225272526607, 360582224893914252, 360582224676461022, 360582224563693912, 360582224447186091]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 78790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 78700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 78700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk787B
