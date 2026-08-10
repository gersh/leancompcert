import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk794A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk794B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk794A

def state06 : KState := ⟨⟨362500023392263130, 362500118020829314⟩, ⟨(-1190084437309483256), (-1185006987942296252)⟩, true⟩

def words05 : List Nat := [371285203899545516, 371285204095813228, 371285204354062238, 371285204402136752, 371285204424003066, 371285204446776935, 371285204534090338, 371285204576422204, 371285204765969058, 371285204956710536]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 79450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 79400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486072633272597, 362486167286628207⟩, ⟨(-81512535544065059), (-76433116285528439)⟩, true⟩

def words06 : List Nat := [371285205147167412, 371285205149913192, 371285205289169306, 371285205430160578, 371285205591111677, 371285205593857149, 371285205543956427, 371285205494934648, 371285205497682262, 371285205512946166]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 79460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 79400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470010607993146, 362470105286109124⟩, ⟨1195036920253821158, 1200118307346698508⟩, true⟩

def words07 : List Nat := [371285205592634245, 371285205673441620, 371285205742791205, 371285205745537176, 371285205624048095, 371285205484012874, 371285205342590183, 371285205287038536, 371285205099394828, 371285204912522646]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 79470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 79400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486377624147267, 362486472326850933⟩, ⟨(-105847647110933345), (-100764305667359937)⟩, true⟩

def words08 : List Nat := [371285204724407129, 371285204695629137, 371285204649863071, 371285204696316507, 371285204703171717, 371285204705936558, 371285204570515400, 371285204571940898, 371285204689013919, 371285204707803905]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 79480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 79400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479074039350292, 362479168767068144⟩, ⟨474810591107119546, 479895921054845388⟩, true⟩

def words09 : List Nat := [371285204725783903, 371285204744726009, 371285204920611547, 371285205018543372, 371285205144570207, 371285205271668074, 371285205373105073, 371285205375851664, 371285205266302007, 371285205193748080]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 79490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 79400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 79400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk794B
