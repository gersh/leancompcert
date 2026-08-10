import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk994A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk994B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk994A

def state06 : KState := ⟨⟨362482171420721715, 362482322266956900⟩, ⟨292052881086307218, 302182123605199040⟩, true⟩

def words05 : List Nat := [371285360180749097, 371285360300610944, 371285360419216049, 371285360422712276, 371285360418151016, 371285360434214021, 371285360541079971, 371285360544576300, 371285360521274363, 371285360494622346]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490391451648252, 362490542329218703⟩, ⟨(-525549425901336716), (-515417066619489732)⟩, true⟩

def words06 : List Nat := [371285360526687812, 371285360556017644, 371285360609578991, 371285360664541423, 371285360705571190, 371285360709069233, 371285360631741087, 371285360620200300, 371285360692208213, 371285360747987797]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484845776050390, 362484996685478441⟩, ⟨26119397252349313, 36254925574051737⟩, true⟩

def words07 : List Nat := [371285360801380312, 371285360855999149, 371285360960982963, 371285361021365392, 371285361090655945, 371285361161265250, 371285361210955118, 371285361214451978, 371285361129142958, 371285361129844888]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480987948969045, 362481138889561674⟩, ⟨409923780655032784, 420062409389905668⟩, true⟩

def words08 : List Nat := [371285361211588598, 371285361215085537, 371285361166059792, 371285361118225020, 371285361068971922, 371285361044974375, 371285360991860009, 371285361018490778, 371285361043036002, 371285361046656758]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487782421520037, 362487933393700040⟩, ⟨(-266115387118716631), (-255973615596317999)⟩, true⟩

def words09 : List Nat := [371285361006632335, 371285360998416639, 371285361054572192, 371285361058069661, 371285360992325334, 371285360893346946, 371285360792914768, 371285360795080433, 371285360790646312, 371285360820403327]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk994B
