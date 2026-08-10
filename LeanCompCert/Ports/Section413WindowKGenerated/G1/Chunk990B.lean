import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk990A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk990B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk990A

def state06 : KState := ⟨⟨362484806798945984, 362484956388277435⟩, ⟨29447826729765529, 39452308671194273⟩, true⟩

def words05 : List Nat := [371285354207367207, 371285354242792285, 371285354378797026, 371285354465384204, 371285354555644183, 371285354647267641, 371285354717355694, 371285354720836235, 371285354654797843, 371285354655072017]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479753569229370, 362479903189540431⟩, ⟨530039452411093568, 540047003352749304⟩, true⟩

def words06 : List Nat := [371285354701273510, 371285354704754336, 371285354619406754, 371285354535074312, 371285354449307180, 371285354395679528, 371285354325640585, 371285354339368878, 371285354351812433, 371285354355416607]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487040162311229, 362487189814180717⟩, ⟨(-191905868057751312), (-181895190468290228)⟩, true⟩

def words07 : List Nat := [371285354302795182, 371285354294163697, 371285354338184416, 371285354341665763, 371285354263108401, 371285354168763189, 371285354073034905, 371285354031074587, 371285353968588814, 371285353991061570]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483698378820381, 362483848062113536⟩, ⟨139173301864763045, 149187093069954977⟩, true⟩

def words08 : List Nat := [371285354007224783, 371285354010706519, 371285353902056049, 371285353897080909, 371285353890462258, 371285353883678235, 371285353795211352, 371285353707869236, 371285353629732204, 371285353633746092]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471802640409706, 362471952355045774⟩, ⟨1318034744880372636, 1328051642017072260⟩, true⟩

def words09 : List Nat := [371285353703166304, 371285353789231218, 371285353848065237, 371285353851547340, 371285353774474743, 371285353729876254, 371285353712965025, 371285353716447202, 371285353612950042, 371285353481604978]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk990B
