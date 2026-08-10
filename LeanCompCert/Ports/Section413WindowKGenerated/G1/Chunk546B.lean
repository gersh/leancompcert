import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk546A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk546B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk546A

def state06 : KState := ⟨⟨362478902951015605, 362478946433067579⟩, ⟨323829084079306827, 325434670584077109⟩, true⟩

def words05 : List Nat := [371284899530924036, 371284899667280378, 371284899972811497, 371284900111750151, 371284900279776473, 371284900448557464, 371284900615916299, 371284900617753320, 371284900339055476, 371284900232383058]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 54650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 54600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475157071258620, 362475200569692429⟩, ⟨528578741456863171, 530185223478646743⟩, true⟩

def words06 : List Nat := [371284900298221402, 371284900300058696, 371284900066569274, 371284899767553096, 371284899467836199, 371284899204945325, 371284898774626367, 371284898679379540, 371284898583533097, 371284898488541499]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 54660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 54600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496757294671838, 362496800809716218⟩, ⟨(-652414903321829694), (-650807513116284166)⟩, true⟩

def words07 : List Nat := [371284898373765979, 371284898437355645, 371284898834210136, 371284898836047882, 371284898787439502, 371284898686273884, 371284898590668384, 371284898592703034, 371284898695106001, 371284898914851160]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 54670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 54600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481620475294870, 362481664006924021⟩, ⟨175300812765939915, 176909109910754189⟩, true⟩

def words08 : List Nat := [371284899071426831, 371284899073268858, 371284898981417280, 371284899082000728, 371284899283720146, 371284899285559309, 371284899103467666, 371284898922320486, 371284898766391216, 371284898768487575]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 54680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 54600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477220562842249, 362477264111021435⟩, ⟨415964209935875456, 417573412286104976⟩, true⟩

def words09 : List Nat := [371284898727356536, 371284898746087097, 371284898747474987, 371284898734424944, 371284898464848208, 371284898298357600, 371284898268471145, 371284898270341757, 371284898131756011, 371284897994244216]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 54690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 54600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 54600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk546B
