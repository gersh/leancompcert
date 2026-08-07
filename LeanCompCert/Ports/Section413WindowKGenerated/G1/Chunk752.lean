import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk752

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485625550927188, 362485709945464920⟩, ⟨(-39897429037290629), (-35611592127193201)⟩, true⟩

def state01 : KState := ⟨⟨362475933861977345, 362476018279897278⟩, ⟨688917058270883725, 693204653639993437⟩, true⟩

def words00 : List Nat := [371285236395324497, 371285236368613761, 371285236157813449, 371285236109872998, 371285236060662471, 371285236035692433, 371285235810018666, 371285235548578783, 371285235286012010, 371285235201232739]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 75200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 75200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476301565255950, 362476386006435860⟩, ⟨661289435948346558, 665578780822949500⟩, true⟩

def words01 : List Nat := [371285235134472923, 371285235191289171, 371285235234514415, 371285235237102976, 371285235044692334, 371285234860036365, 371285234674008321, 371285234665397852, 371285234549541929, 371285234434790327]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 75210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 75200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479139766229805, 362479224230599334⟩, ⟨447847865464162377, 452138954781313365⟩, true⟩

def words02 : List Nat := [371285234318918659, 371285234292732535, 371285234288340808, 371285234376360705, 371285234407462302, 371285234410053495, 371285234264350406, 371285234281949176, 371285234316378277, 371285234319058477]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 75220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 75200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479229099387095, 362479313587404894⟩, ⟨441137005118619698, 445429873609549084⟩, true⟩

def words03 : List Nat := [371285234241132912, 371285234163078966, 371285234128050960, 371285234130903997, 371285234088536859, 371285234071704964, 371285234053975565, 371285234036798651, 371285233783394004, 371285233708000449]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 75230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 75200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475834848302444, 362475919359404473⟩, ⟨696546438631602503, 700841044100649015⟩, true⟩

def words04 : List Nat := [371285233704707375, 371285233707303850, 371285233602093986, 371285233462263455, 371285233321455198, 371285233211201893, 371285233011608032, 371285232962926505, 371285232913357931, 371285232861651658]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 75240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 75200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362479920818594909, 362480005353056958⟩, ⟨389082631525168467, 393378994955256815⟩, true⟩

def words05 : List Nat := [371285232739654325, 371285232710157095, 371285232823187754, 371285232825777638, 371285232754744611, 371285232652697903, 371285232549612052, 371285232489901401, 371285232352853931, 371285232286287828]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 75250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 75200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477240993463517, 362477325551299528⟩, ⟨590744486391120600, 595042609060099398⟩, true⟩

def words06 : List Nat := [371285232218773214, 371285232152043251, 371285231929697508, 371285231867816020, 371285231804561181, 371285231795854512, 371285231551295017, 371285231306752133, 371285231061182976, 371285230993162955]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 75260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 75200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472445075899210, 362472529657117460⟩, ⟨951758430981317982, 956058313748254480⟩, true⟩

def words07 : List Nat := [371285230889924376, 371285230861481162, 371285230832153762, 371285230768557067, 371285230493637200, 371285230273846545, 371285230052705580, 371285230008756700, 371285229853613088, 371285229687852692]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 75270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 75200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481901709871046, 362481986314249878⟩, ⟨239842806885357826, 244144433300988580⟩, true⟩

def words08 : List Nat := [371285229520908537, 371285229514295342, 371285229437291323, 371285229458956314, 371285229461015639, 371285229434469608, 371285229171996550, 371285229068132250, 371285229032158535, 371285229034840940]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 75280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 75200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362467661401146484, 362467746029148897⟩, ⟨1312108313345604647, 1316411718498615011⟩, true⟩

def words09 : List Nat := [371285228993708765, 371285228953553372, 371285228945095262, 371285228947978691, 371285228910584315, 371285228866557381, 371285228821610528, 371285228771452587, 371285228485472277, 371285228256486197]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 75290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 75200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 75200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk752
