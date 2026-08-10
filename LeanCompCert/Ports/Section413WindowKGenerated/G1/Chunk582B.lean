import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk582A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk582B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk582A

def state06 : KState := ⟨⟨362500164955841211, 362500214606304219⟩, ⟨(-887795645080633543), (-885841662818583307)⟩, true⟩

def words05 : List Nat := [371285006172744097, 371285006530862043, 371285007082584323, 371285007562353861, 371285008111484266, 371285008661388429, 371285009211756604, 371285009369661814, 371285009631991685, 371285009895385791]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 58250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 58200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474240019138870, 362474289687142813⟩, ⟨622699213935784564, 624654218224565462⟩, true⟩

def words06 : List Nat := [371285010179110728, 371285010181078404, 371285010072025260, 371285009962274235, 371285009851757461, 371285009811415611, 371285009671040772, 371285009677530637, 371285009681986463, 371285009684023276]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 58260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 58200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495284173321982, 362495333859129925⟩, ⟨(-603634501364684690), (-601678459548273226)⟩, true⟩

def words07 : List Nat := [371285009612342219, 371285009725672693, 371285010053948025, 371285010055915970, 371285009991701866, 371285009835697257, 371285009766556741, 371285009768739822, 371285009930002676, 371285010109373602]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 58270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 58200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482436887098012, 362482486590672758⟩, ⟨145190474764981754, 147147552122562948⟩, true⟩

def words08 : List Nat := [371285010286692605, 371285010288698067, 371285010512235855, 371285010754313587, 371285011083924232, 371285011085892748, 371285011055314979, 371285011024184579, 371285010993162489, 371285010995409807]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 58280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 58200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468546705339901, 362468596426629067⟩, ⟨954983157810520089, 956941267829191235⟩, true⟩

def words09 : List Nat := [371285011162258866, 371285011373204928, 371285011542374302, 371285011544343258, 371285011320997869, 371285011158279303, 371285011069787795, 371285011071757006, 371285010792895287, 371285010513555812]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 58290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 58200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 58200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk582B
