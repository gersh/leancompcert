import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk778A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk778B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk778A

def state06 : KState := ⟨⟨362480324770639927, 362480415484775142⟩, ⟨369562684705870956, 374332213359036416⟩, true⟩

def words05 : List Nat := [371285222997546434, 371285223106492093, 371285223214567572, 371285223217301261, 371285223224245490, 371285223241502744, 371285223345317314, 371285223348021928, 371285223303777502, 371285223245028919]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 77850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 77800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487257104021511, 362487347842234527⟩, ⟨(-170202605215151320), (-165431201743016336)⟩, true⟩

def words06 : List Nat := [371285223185135423, 371285223184508781, 371285223219594726, 371285223321595071, 371285223394020946, 371285223396707695, 371285223264530284, 371285223283228526, 371285223385840835, 371285223415917375]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 77860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 77800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486300372635429, 362486391135333449⟩, ⟨(-95686942210284804), (-90913631970637132)⟩, true⟩

def words07 : List Nat := [371285223434031849, 371285223453090861, 371285223608100561, 371285223681782084, 371285223754476301, 371285223828138040, 371285223882291472, 371285223884982510, 371285223776641002, 371285223795006918]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 77870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 77800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481344618050075, 362481435404700960⟩, ⟨290330478732316011, 295105654548294809⟩, true⟩

def words08 : List Nat := [371285223934016835, 371285223936879600, 371285223938898041, 371285223939142707, 371285223963472166, 371285223966461374, 371285224000434816, 371285224092212067, 371285224150853775, 371285224153635975]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 77880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 77800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362503665282644109, 362503756093560528⟩, ⟨(-1448359631548610426), (-1443582565568870776)⟩, true⟩

def words09 : List Nat := [371285224115526128, 371285224127409096, 371285224302668198, 371285224352508649, 371285224371065908, 371285224390527676, 371285224547934565, 371285224624071441, 371285224863782391, 371285225104669900]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 77890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 77800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 77800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk778B
