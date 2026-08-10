import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk541A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk541B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk541A

def state06 : KState := ⟨⟨362466319962113859, 362466362620776047⟩, ⟨1005677671332618842, 1007238456758748296⟩, true⟩

def words05 : List Nat := [371284961139939706, 371284961329582380, 371284961445547819, 371284961447366135, 371284961109058245, 371284960875996214, 371284960693916781, 371284960695743871, 371284960422523307, 371284960081203646]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 54150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 54100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494716290629080, 362494758965568238⟩, ⟨(-532359899917196516), (-530798232848466578)⟩, true⟩

def words06 : List Nat := [371284959739064627, 371284959657160349, 371284959559605278, 371284959682339628, 371284959717951686, 371284959719802763, 371284959669006834, 371284959815316764, 371284960214694457, 371284960397462638]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 54160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 54100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481664776007715, 362481707467542886⟩, ⟨174728802392664650, 176291368548904560⟩, true⟩

def words07 : List Nat := [371284960581466963, 371284960766043885, 371284961057545467, 371284961179398707, 371284961321004792, 371284961463316796, 371284961605398104, 371284961607217393, 371284961334250281, 371284961276486203]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 54170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 54100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469492461726405, 362469535169451940⟩, ⟨834339030405133706, 835902473840308880⟩, true⟩

def words08 : List Nat := [371284961497716744, 371284961499535989, 371284961327253598, 371284961156067058, 371284960984165577, 371284960917366882, 371284960728677989, 371284960682603095, 371284960635938512, 371284960570334766]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 54180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 54100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499362475804974, 362499405199996234⟩, ⟨(-784432469903796677), (-782868134107518257)⟩, true⟩

def words09 : List Nat := [371284960290460160, 371284960296200204, 371284960640887934, 371284960725831639, 371284960754995022, 371284960784712054, 371284960911043300, 371284960913067070, 371284961136418711, 371284961404972019]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 54190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 54100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 54100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk541B
