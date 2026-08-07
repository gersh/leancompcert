import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk157

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487801352846140, 362487804582984192⟩, ⟨(-59461238950355103), (-59426934035099237)⟩, true⟩

def state01 : KState := ⟨⟨362495202474949738, 362495205709368355⟩, ⟨(-175605366092879572), (-175570993951139330)⟩, true⟩

def words00 : List Nat := [371284021553417812, 371284021553943512, 371284024281097748, 371284027135735978, 371284029258231590, 371284029258709306, 371284026337136305, 371284026692863683, 371284029961327553, 371284030673154802]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 15700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 15700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479345543204443, 362479348781978373⟩, ⟨73719434005131547, 73753874591037547⟩, true⟩

def words01 : List Nat := [371284031374463688, 371284032075850504, 371284035698483414, 371284037354376045, 371284039248561290, 371284041142677722, 371284043102753395, 371284043103231994, 371284040802160269, 371284040504280602]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 15710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 15700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487020349380818, 362487023592420064⟩, ⟨(-46859207127346645), (-46824699468295433)⟩, true⟩

def words02 : List Nat := [371284043548829296, 371284043563697161, 371284043593866906, 371284043624186136, 371284043624523850, 371284043610856388, 371284043610631177, 371284045632070373, 371284046815093736, 371284047004824343]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 15720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 15700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362619463486675583, 362619466734028689⟩, ⟨(-2130854294435088881), (-2130819718896919735)⟩, true⟩

def words03 : List Nat := [371284051235449770, 371284055465785625, 371284063735916295, 371284066626025580, 371284068895838837, 371284071165525090, 371284077473734863, 371284082037898222, 371284090639538300, 371284099240292782]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 15730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 15700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362533575180404892, 362533578432089067⟩, ⟨(-778843263826554267), (-778808620096202409)⟩, true⟩

def words04 : List Nat := [371284107126964570, 371284110963539647, 371284115742227752, 371284120520555291, 371284126111360131, 371284126329221266, 371284126329579806, 371284126296735465, 371284130265173343, 371284133405100546]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 15740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 15700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362426242129510598, 362426245385509603⟩, ⟨912516516614772350, 912551228325944454⟩, true⟩

def words05 : List Nat := [371284139457524494, 371284145509380788, 371284151190561462, 371284151503708237, 371284152169062069, 371284152834563828, 371284155127496649, 371284155127975964, 371284152055968051, 371284148382230793]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 15750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 15700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474502277867187, 362474505538156114⟩, ⟨151863935636330890, 151898714978379688⟩, true⟩

def words06 : List Nat := [371284145063746510, 371284145064274501, 371284144165572334, 371284144712235199, 371284144712606270, 371284144653167952, 371284139234103551, 371284137841048159, 371284137669236266, 371284137669733691]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 15760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 15700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362531897019289632, 362531900283949024⟩, ⟨(-753563252137683916), (-753528403851187976)⟩, true⟩

def words07 : List Nat := [371284137059349052, 371284135680859921, 371284136945808689, 371284138157167738, 371284140576464202, 371284142995644867, 371284145436798955, 371284145437287937, 371284148166513979, 371284151193026321]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 15770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 15700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362496426848535158, 362496430117466199⟩, ⟨(-193532186052091304), (-193497270336290602)⟩, true⟩

def words08 : List Nat := [371284157416993262, 371284159864327375, 371284162295491912, 371284164726514061, 371284166146044869, 371284166146578335, 371284168976296335, 371284172398047075, 371284175698328417, 371284176474863686]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 15780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 15700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362565802931949453, 362565806205234467⟩, ⟨(-1289157866936215408), (-1289122882449899162)⟩, true⟩

def words09 : List Nat := [371284181264116079, 371284186053025513, 371284193295580636, 371284195923426890, 371284198179704941, 371284200435840157, 371284206701793026, 371284210984252284, 371284216148839115, 371284221312983983]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 15790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 15700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 15700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk157
