import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk528

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483769359633930, 362483809820015933⟩, ⟨63414744348214688, 64857958654550962⟩, true⟩

def state01 : KState := ⟨⟨362470440191547372, 362470480667702577⟩, ⟨767257398175427450, 768701445388120818⟩, true⟩

def words00 : List Nat := [371285038233843494, 371285038235617882, 371285037936585504, 371285037637825704, 371285037338416243, 371285037099205510, 371285036725540124, 371285036710805721, 371285036695423917, 371285036650383663]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 52800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 52800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486116741196217, 362486157233327756⟩, ⟨(-60687985602003599), (-59243094597467997)⟩, true⟩

def words01 : List Nat := [371285036375969056, 371285036285687178, 371285036460177930, 371285036461947945, 371285036251501190, 371285035956408577, 371285035721596751, 371285035723547207, 371285035627895235, 371285035651104825]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 52810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 52800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477772704498055, 362477813212622736⟩, ⟨380099961922233048, 381545697765582026⟩, true⟩

def words02 : List Nat := [371285035673497963, 371285035675311685, 371285035617910865, 371285035743502617, 371285035975342627, 371285035977113355, 371285035783630253, 371285035591037301, 371285035397768836, 371285035353409516]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 52820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 52800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362465855710252251, 362465896234345489⟩, ⟨1009782273408726680, 1011228852950746404⟩, true⟩

def words03 : List Nat := [371285035336677035, 371285035457394344, 371285035509939766, 371285035511710373, 371285035087021726, 371285034773174328, 371285034500168316, 371285034501940748, 371285034157981838, 371285033797800273]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 52830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 52800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475614487866004, 362475655027837697⟩, ⟨494106153928745146, 495553572569549248⟩, true⟩

def words04 : List Nat := [371285033436829811, 371285033379946004, 371285033143391251, 371285033055651066, 371285032967373512, 371285032851018887, 371285032257194318, 371285031959300795, 371285031660458660, 371285031632805901]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 52840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 52800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481762136799412, 362481802692873944⟩, ⟨169153928280379621, 170602198039641409⟩, true⟩

def words05 : List Nat := [371285031456714901, 371285031261887235, 371285031094504711, 371285031096459364, 371285030976245276, 371285030875962538, 371285030775106491, 371285030603706245, 371285030186453880, 371285030127570116]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 52850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 52800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476187655771641, 362476228227632188⟩, ⟨463868222996179732, 465317327284021496⟩, true⟩

def words06 : List Nat := [371285030364032537, 371285030365804297, 371285030186817806, 371285029977756999, 371285029767967270, 371285029629631411, 371285029373185799, 371285029379596783, 371285029385756848, 371285029387595949]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 52860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 52800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482204940196682, 362482245528110027⟩, ⟨145663103416487287, 147113056497572919⟩, true⟩

def words07 : List Nat := [371285029222361014, 371285029141856211, 371285029251162700, 371285029252934824, 371285028968665552, 371285028626041449, 371285028282738921, 371285028004175969, 371285027595660398, 371285027545063461]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 52870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 52800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468921987470960, 362468962591363934⟩, ⟨848072948540447772, 849523746704908504⟩, true⟩

def words08 : List Nat := [371285027493779879, 371285027443351694, 371285026955358167, 371285026825361163, 371285026694505199, 371285026580501480, 371285026062456707, 371285025482076955, 371285024900970400, 371285024677707381]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 52880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 52800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362446640733112309, 362446681352980689⟩, ⟨2026762029352159855, 2028213672535363187⟩, true⟩

def words09 : List Nat := [371285024379268360, 371285024385249207, 371285024393208585, 371285024394981952, 371285023982438540, 371285023641911192, 371285023300452648, 371285023187872037, 371285022598898685, 371285021876090999]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 52890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 52800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 52800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk528
