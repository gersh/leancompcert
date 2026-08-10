import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk543A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk543B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk543A

def state06 : KState := ⟨⟨362462294885486381, 362462337872563665⟩, ⟨1226571748127305319, 1228150353416302157⟩, true⟩

def words05 : List Nat := [371284933237696258, 371284933017722943, 371284932796997903, 371284932735632580, 371284932504334495, 371284932289035873, 371284932073146073, 371284931858006601, 371284931191581206, 371284930778255650]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 54350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 54300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472767626084791, 362472810629451813⟩, ⟨657304622184155784, 658884113068282818⟩, true⟩

def words06 : List Nat := [371284930363886021, 371284930288039823, 371284930023918883, 371284929760736735, 371284929496882716, 371284929317315292, 371284929096676436, 371284929156654616, 371284929158057123, 371284929152774754]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 54360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 54300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497146058842530, 362497189078700557⟩, ⟨(-668254582191964839), (-666674194608417349)⟩, true⟩

def words07 : List Nat := [371284929046035059, 371284929163105611, 371284929451562950, 371284929453390894, 371284929360033544, 371284929207449206, 371284929237190784, 371284929302445287, 371284929529137725, 371284929756609967]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 54370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 54300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470200356888819, 362470243393245696⟩, ⟨797097118278914984, 798678403151825326⟩, true⟩

def words08 : List Nat := [371284929983729309, 371284929985556029, 371284929762234128, 371284929600163436, 371284929437157377, 371284929350857272, 371284928859325348, 371284928367435578, 371284927874838238, 371284927680856504]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 54380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 54300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362443033068698740, 362443076121522921⟩, ⟨2274960908816505868, 2276543089428326524⟩, true⟩

def words09 : List Nat := [371284927453886924, 371284927497660125, 371284927541126175, 371284927542953182, 371284927136222051, 371284926688441078, 371284926239755006, 371284925875591280, 371284925107274394, 371284924340078589]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 54390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 54300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 54300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk543B
