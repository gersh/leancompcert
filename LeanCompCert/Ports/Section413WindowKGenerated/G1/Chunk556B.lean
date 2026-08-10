import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk556A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk556B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk556A

def state06 : KState := ⟨⟨362441779252060404, 362441824405391021⟩, ⟨2398600844419124312, 2400298621553806754⟩, true⟩

def words05 : List Nat := [371284953262265888, 371284953023253866, 371284952783642326, 371284952535629746, 371284951857176211, 371284951278341155, 371284950698541703, 371284950253765137, 371284949479583783, 371284948706892168]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 55650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 55600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474409528227978, 362474454698309844⟩, ⟨582274332001776447, 583973041597590467⟩, true⟩

def words06 : List Nat := [371284947933396147, 371284947482909889, 371284946869933590, 371284946579984765, 371284946289416263, 371284945948148603, 371284945296819375, 371284944968618750, 371284944639480290, 371284944603853182]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 55660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 55600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476409202953950, 362476454390152616⟩, ⟨470936907539397115, 472636570110324761⟩, true⟩

def words07 : List Nat := [371284944416861277, 371284944120642347, 371284943847482132, 371284943849567870, 371284943715591015, 371284943602588822, 371284943488974390, 371284943350404579, 371284942984402068, 371284942834299713]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 55670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 55600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470215939868082, 362470261143728871⟩, ⟨815865958401158080, 817566548807961074⟩, true⟩

def words08 : List Nat := [371284942852664404, 371284942854551133, 371284942736453808, 371284942592808264, 371284942448492081, 371284942282296959, 371284941953721837, 371284941912353132, 371284941870340343, 371284941814384428]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 55680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 55600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483182973495309, 362483228194313213⟩, ⟨93693555222803463, 95395090053980603⟩, true⟩

def words09 : List Nat := [371284941610334145, 371284941670917793, 371284941845391997, 371284941847266490, 371284941592617157, 371284941294720151, 371284941017938374, 371284941020003966, 371284940881680052, 371284940853021543]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 55690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 55600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 55600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk556B
