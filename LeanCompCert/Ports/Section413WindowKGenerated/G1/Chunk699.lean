import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk699

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478344299007640, 362478416803127494⟩, ⟨481600406602587074, 485023180299120508⟩, true⟩

def state01 : KState := ⟨⟨362466004717581062, 362466077243040995⟩, ⟨1344228112961383621, 1347652378441151247⟩, true⟩

def words00 : List Nat := [371285355520664235, 371285355520459645, 371285355348935762, 371285355178276267, 371285355006679871, 371285354823702356, 371285354547559354, 371285354447741957, 371285354347172131, 371285354204540654]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 69900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 69900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494539871571114, 362494612418707292⟩, ⟨(-650790246773682068), (-647364465802634556)⟩, true⟩

def words01 : List Nat := [371285353930428226, 371285353861749291, 371285353905469629, 371285353907874577, 371285353828303445, 371285353708931327, 371285353656056735, 371285353658695550, 371285353770867712, 371285353906017219]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 69910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 69900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473147038246712, 362473219607017539⟩, ⟨845033167772237058, 848460461547747938⟩, true⟩

def words02 : List Nat := [371285354016955019, 371285354019348965, 371285353857792011, 371285353777969759, 371285353696994093, 371285353680524262, 371285353391169286, 371285353060953782, 371285352729752182, 371285352603750669]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 69920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 69900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362467347440274582, 362467420030571663⟩, ⟨1250691613610952154, 1254120412826822904⟩, true⟩

def words03 : List Nat := [371285352462380516, 371285352495461676, 371285352528278142, 371285352530672695, 371285352321289386, 371285352167606468, 371285352012680076, 371285351906818816, 371285351659925803, 371285351406219745]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 69930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 69900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477484307113666, 362477556918823571⟩, ⟨541728804703140889, 545159101642261129⟩, true⟩

def words04 : List Nat := [371285351151465083, 371285351101689284, 371285350948534567, 371285350943261134, 371285350937175167, 371285350898937480, 371285350621665428, 371285350537216525, 371285350470332408, 371285350472814169]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 69940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 69900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362483678138429268, 362483750772012974⟩, ⟨108408509543575069, 111840336663587919⟩, true⟩

def words05 : List Nat := [371285350363220939, 371285350211902831, 371285350059588017, 371285350042967592, 371285349932880890, 371285349839181198, 371285349744715640, 371285349649535464, 371285349424454064, 371285349404612511]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 69950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 69900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471081070095339, 362471153724987535⟩, ⟨989786863038320337, 993220181012215673⟩, true⟩

def words06 : List Nat := [371285349532027042, 371285349534422246, 371285349412820157, 371285349292532306, 371285349171381429, 371285349059242340, 371285348878179114, 371285348808665413, 371285348738313538, 371285348668263400]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 69960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 69900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475838053174276, 362475910729716135⟩, ⟨656944497744323542, 660379330654942192⟩, true⟩

def words07 : List Nat := [371285348467030241, 371285348373166452, 371285348362125351, 371285348364521391, 371285348205081762, 371285348014697327, 371285347823327249, 371285347731019777, 371285347548531694, 371285347416350244]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 69970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 69900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467524524830213, 362467597222988681⟩, ⟨1238762936410746124, 1242199282161809054⟩, true⟩

def words08 : List Nat := [371285347283294721, 371285347151387468, 371285346835133583, 371285346691769783, 371285346547160379, 371285346465542657, 371285346213114921, 371285345937840027, 371285345661626593, 371285345462482349]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 69980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 69900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362461541391089162, 362461614110877408⟩, ⟨1657599102212988949, 1661036961939821163⟩, true⟩

def words09 : List Nat := [371285345210528863, 371285345163261682, 371285345115213855, 371285344988058795, 371285344614051863, 371285344303459772, 371285343991654442, 371285343884271045, 371285343546550264, 371285343210333692]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 69990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 69900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 69900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk699
