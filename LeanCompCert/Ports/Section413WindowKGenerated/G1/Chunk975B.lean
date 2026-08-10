import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk975A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk975B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk975A

def state06 : KState := ⟨⟨362490915269199520, 362491060193227355⟩, ⟨(-567231169785575078), (-557685343923350468)⟩, true⟩

def words05 : List Nat := [371285342714030195, 371285342816705306, 371285343022989120, 371285343182135724, 371285343368966397, 371285343557077918, 371285343746135508, 371285343796001190, 371285343856974130, 371285343919881209]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 97550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 97500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488086589433239, 362488231543969158⟩, ⟨(-291246889308294589), (-281698086917821437)⟩, true⟩

def words06 : List Nat := [371285344085914756, 371285344113006331, 371285344126769274, 371285344141651132, 371285344169975617, 371285344173821558, 371285344246705429, 371285344328964374, 371285344402068704, 371285344435228674]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 97560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 97500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502951739512510, 362503096724996123⟩, ⟨(-1741733149095702114), (-1732181326984429420)⟩, true⟩

def words07 : List Nat := [371285344572237858, 371285344710985643, 371285344881382414, 371285344912829307, 371285344926307620, 371285344940880183, 371285345059114119, 371285345139781245, 371285345324021795, 371285345509831446]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 97570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 97500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491175567311410, 362491320583662549⟩, ⟨(-592583049123775783), (-583028214801612945)⟩, true⟩

def words08 : List Nat := [371285345674991239, 371285345712116978, 371285345853220153, 371285345996153794, 371285346159046531, 371285346195987892, 371285346211209831, 371285346227491719, 371285346317895259, 371285346383021080]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 97580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 97500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484295032890614, 362484440080123163⟩, ⟨78966237219810904, 88524085416136252⟩, true⟩

def words09 : List Nat := [371285346515695153, 371285346649806777, 371285346782471220, 371285346828693823, 371285346895730415, 371285346964462101, 371285347097665952, 371285347101091909, 371285347094582666, 371285347089195050]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 97590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 97500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 97500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk975B
