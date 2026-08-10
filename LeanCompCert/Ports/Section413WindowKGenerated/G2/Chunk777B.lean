import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk777A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk777B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk777A

def state06 : KState := ⟨⟨360584673441586103, 360584712738426327⟩, ⟨(-197488952187027654), (-195425113556338310)⟩, true⟩

def words05 : List Nat := [360582198817863672, 360582198872099334, 360582198975466156, 360582199161869079, 360582199306574278, 360582199451475942, 360582199513537930, 360582199520878500, 360582199554102328, 360582199587700947]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 77750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 77700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593107279534738, 360593146586845023⟩, ⟨(-853399017218732644), (-851334364384947358)⟩, true⟩

def words06 : List Nat := [360582199786087464, 360582199874475753, 360582199875483957, 360582199828466714, 360582199781269962, 360582199665930042, 360582199719179827, 360582199783165650, 360582199784164213, 360582199905377832]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 77760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 77700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599388731422846, 360599428049203338⟩, ⟨(-1341896788120147994), (-1339831320966389704)⟩, true⟩

def words07 : List Nat := [360582200174370306, 360582200443681531, 360582200877779093, 360582201217161803, 360582201391425284, 360582201565766254, 360582201685866164, 360582201915149407, 360582202137524690, 360582202360140889]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 77770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 77700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360597989786679370, 360598029115028812⟩, ⟨(-1233212387779321149), (-1231146098520429901)⟩, true⟩

def words08 : List Nat := [360582202456784242, 360582202457894607, 360582202485415634, 360582202582516072, 360582202609080022, 360582202652814738, 360582202653814996, 360582202585766806, 360582202579522224, 360582202784238356]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 77780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 77700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585670450542119, 360585709789365213⟩, ⟨(-274854632739540270), (-272787528681905372)⟩, true⟩

def words09 : List Nat := [360582202984585919, 360582203185141121, 360582203302921286, 360582203304031912, 360582203304698369, 360582203264284137, 360582203346911103, 360582203475720762, 360582203521778684, 360582203567996826]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 77790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 77700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 77700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk777B
