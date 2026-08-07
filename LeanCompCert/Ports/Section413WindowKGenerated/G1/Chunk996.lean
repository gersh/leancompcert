import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk996

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488601591894993, 362488752879617402⟩, ⟨(-347932869390157879), (-337759685594871527)⟩, true⟩

def state01 : KState := ⟨⟨362484142654640055, 362484293973574813⟩, ⟨96192263809430943, 106368556518477415⟩, true⟩

def words00 : List Nat := [371285361876990450, 371285361880492272, 371285361871286117, 371285361839956721, 371285361807332077, 371285361781136623, 371285361748191112, 371285361784773063, 371285361820066557, 371285361823755704]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 99600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 99600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486086377604925, 362486237728159461⟩, ⟨(-97407088423198777), (-87227645907418627)⟩, true⟩

def words01 : List Nat := [371285361905500861, 371285361999782955, 371285362144413325, 371285362155836070, 371285362158548326, 371285362147963125, 371285362145862002, 371285362149722141, 371285362120492905, 371285362133195474]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 99610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 99600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477744151879497, 362477895534036297⟩, ⟨733657584515338957, 743840175409190259⟩, true⟩

def words02 : List Nat := [371285362144538239, 371285362148040881, 371285362024808762, 371285362004291559, 371285361986516739, 371285361990019649, 371285361874919616, 371285361741936203, 371285361607560826, 371285361560086776]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 99620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 99600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362473060270392000, 362473211684168178⟩, ⟨1200337232656555633, 1210522973947912709⟩, true⟩

def words03 : List Nat := [371285361487567411, 371285361445213405, 371285361401611758, 371285361358819172, 371285361201509073, 371285361076326681, 371285360949358406, 371285360887363361, 371285360768144382, 371285360650185319]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 99630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 99600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479323787479094, 362479475232601171⟩, ⟨576248681867062491, 586437546622548545⟩, true⟩

def words04 : List Nat := [371285360530634290, 371285360490958448, 371285360406382178, 371285360417054878, 371285360419826530, 371285360419454055, 371285360283711580, 371285360241274268, 371285360201840917, 371285360205472446]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 99640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 99600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk996
