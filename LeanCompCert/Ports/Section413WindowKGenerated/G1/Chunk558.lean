import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk558

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474607053662095, 362474652443659719⟩, ⟨571656488676864080, 573367455297019514⟩, true⟩

def state01 : KState := ⟨⟨362463900440580645, 362463945847301823⟩, ⟨1169144762699543969, 1170856662580776699⟩, true⟩

def words00 : List Nat := [371284927720214275, 371284927722092272, 371284927352837540, 371284926918891706, 371284926484224820, 371284926148474471, 371284925668595756, 371284925510124661, 371284925351020493, 371284925181875928]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 55800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 55800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496271210919612, 362496316634610343⟩, ⟨(-637689100845316288), (-635976253805096798)⟩, true⟩

def words01 : List Nat := [371284924807277097, 371284924462849301, 371284924117481713, 371284924093293333, 371284923836860714, 371284923519046568, 371284923201125506, 371284923203251009, 371284923292249634, 371284923498446443]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 55810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 55800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488452124439707, 362488497565072440⟩, ⟨(-201223479347328378), (-199509686517251182)⟩, true⟩

def words02 : List Nat := [371284923674529890, 371284923676421765, 371284923917104936, 371284924199304349, 371284924415083151, 371284924416962176, 371284924243855477, 371284924070608197, 371284924041766785, 371284924107915713]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 55820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 55800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362471592790116278, 362471638247714725⟩, ⟨740199978317906290, 741914718429485740⟩, true⟩

def words03 : List Nat := [371284924442426418, 371284924777740277, 371284925082916510, 371284925084795732, 371284924962664915, 371284924899652220, 371284925090703044, 371284925092582359, 371284924921886341, 371284924686082016]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 55830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 55800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491839852875734, 362491885327291741⟩, ⟨(-390451742920851286), (-388736063630836638)⟩, true⟩

def words04 : List Nat := [371284924449426480, 371284924451472235, 371284924489468054, 371284924669976035, 371284924779323981, 371284924781236283, 371284924630024979, 371284924638468297, 371284924966102570, 371284925092674083]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 55840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 55800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362495658452462488, 362495703944007201⟩, ⟨(-603752830858093614), (-602036194844870830)⟩, true⟩

def words05 : List Nat := [371284925219199287, 371284925346337002, 371284925570056890, 371284925671628051, 371284925870328329, 371284926069765303, 371284926256691599, 371284926258584179, 371284926351342838, 371284926546630769]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 55850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 55800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480956100681909, 362481001608949442⟩, ⟨217661168138729309, 219378738377439267⟩, true⟩

def words06 : List Nat := [371284926953996167, 371284927111409293, 371284927266254730, 371284927421730866, 371284927674404135, 371284927767451700, 371284927931609670, 371284928096484849, 371284928199777809, 371284928201725126]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 55860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 55800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362514217042018060, 362514262567314610⟩, ⟨(-1640740640119008970), (-1639022118386064976)⟩, true⟩

def words07 : List Nat := [371284928382381155, 371284928634330590, 371284929144473157, 371284929471522639, 371284929733831316, 371284929996697089, 371284930536306347, 371284930934503915, 371284931460690235, 371284931987718933]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 55870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 55800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489921898791581, 362489967441084618⟩, ⟨(-283103794020554343), (-281384322437318993)⟩, true⟩

def words08 : List Nat := [371284932452466106, 371284932491140755, 371284932670572497, 371284932850949241, 371284933128362458, 371284933130243501, 371284932981306583, 371284932825089873, 371284932829459168, 371284932921708738]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 55880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 55800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475293733947012, 362475339293145623⟩, ⟨534569266773474250, 536289683294624566⟩, true⟩

def words09 : List Nat := [371284933177605570, 371284933434232406, 371284933688072760, 371284933689954007, 371284933517400263, 371284933360661364, 371284933363560816, 371284933365446213, 371284933195817365, 371284933026299373]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 55890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 55800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 55800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk558
