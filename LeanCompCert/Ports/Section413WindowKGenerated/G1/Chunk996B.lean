import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk996A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk996B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk996A

def state06 : KState := ⟨⟨362478677437188536, 362478828914232022⟩, ⟨640685903439891434, 650877949326616964⟩, true⟩

def words05 : List Nat := [371285360149035452, 371285360084125079, 371285360039318943, 371285360043191021, 371285360030762557, 371285360039053136, 371285360046185204, 371285360049705957, 371285359960275063, 371285359899073751]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478183537390222, 362478335045605464⟩, ⟨689922235807265365, 700117388436615889⟩, true⟩

def words06 : List Nat := [371285359871098958, 371285359874603156, 371285359778203260, 371285359681474217, 371285359583359601, 371285359513399398, 371285359408785249, 371285359406272809, 371285359402607723, 371285359399858867]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485518935434847, 362485670475410520⟩, ⟨(-41284440224723686), (-31086121877159970)⟩, true⟩

def words07 : List Nat := [371285359331794843, 371285359266133258, 371285359198666808, 371285359156808317, 371285359031054639, 371285358891766512, 371285358751085472, 371285358704228656, 371285358612183084, 371285358619370983]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481306555429023, 362481458127009691⟩, ⟨378607951642285731, 388809420534991181⟩, true⟩

def words08 : List Nat := [371285358621990292, 371285358618331044, 371285358559024153, 371285358578185283, 371285358625957816, 371285358629462954, 371285358543304570, 371285358433017744, 371285358321263708, 371285358311787854]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477315490552385, 362477467093651468⟩, ⟨776541852082513100, 786746463206393272⟩, true⟩

def words09 : List Nat := [371285358327785334, 371285358384300388, 371285358422374675, 371285358425941428, 371285358380258669, 371285358360118776, 371285358380246830, 371285358383752824, 371285358306936669, 371285358231697671]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk996B
