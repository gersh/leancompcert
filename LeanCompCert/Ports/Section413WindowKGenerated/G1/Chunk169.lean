import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk169

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362452444891232909, 362452448658607592⟩, ⟨553520205837207593, 553563272032137789⟩, true⟩

def state01 : KState := ⟨⟨362490181436704252, 362490185208701229⟩, ⟨(-84158294049277530), (-84115149713593316)⟩, true⟩

def words00 : List Nat := [371285203503543974, 371285203504118862, 371285206689313844, 371285210030351463, 371285212325868870, 371285212326386128, 371285210588542438, 371285209805330732, 371285210923734627, 371285211218415995]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 16900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 16900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478557380704371, 362478561157429788⟩, ⟨112570251132845739, 112613475450180577⟩, true⟩

def words01 : List Nat := [371285211525258630, 371285211832251724, 371285214424967819, 371285215283158033, 371285216544619030, 371285217806122568, 371285219046448283, 371285219046969387, 371285217192919431, 371285216800186891]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 16910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 16900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473129843425938, 362473133624764993⟩, ⟨204559810955571463, 204603113359594989⟩, true⟩

def words02 : List Nat := [371285219503503567, 371285219504021337, 371285217953421177, 371285216383545548, 371285214813663241, 371285214348935419, 371285215204517019, 371285217376076552, 371285218864238318, 371285218864774420]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 16920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 16900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362521514646356809, 362521518432380249⟩, ⟨(-614847495792490695), (-614804114058078507)⟩, true⟩

def words03 : List Nat := [371285220923725096, 371285223696404759, 371285226945704941, 371285226946223305, 371285225554269116, 371285223669828283, 371285223385204754, 371285223385780555, 371285225390818279, 371285227533728571]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 16930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 16900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475442262392751, 362475446053086153⟩, ⟨165774461589866280, 165817922457730518⟩, true⟩

def words04 : List Nat := [371285229655907281, 371285229656425994, 371285229488373320, 371285231145655328, 371285233831381871, 371285233831900757, 371285232576440991, 371285230608110162, 371285228820781394, 371285228821372745]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 16940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 16900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362439646627703685, 362439650423072123⟩, ⟨772810824299594620, 772854364432849214⟩, true⟩

def words05 : List Nat := [371285228515177170, 371285228786284231, 371285229038541104, 371285229039068912, 371285226561804988, 371285225114042579, 371285225022084160, 371285225022603132, 371285222352692604, 371285219666258023]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 16950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 16900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485975238063272, 362485979038083337⟩, ⟨(-13023308653734596), (-12979689605212676)⟩, true⟩

def words06 : List Nat := [371285216979909361, 371285215748103470, 371285214319583958, 371285215341908847, 371285216033622917, 371285216034143445, 371285213225476601, 371285212581989924, 371285214176638314, 371285214222244247]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 16960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 16900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362492911687580772, 362492915492321713⟩, ⟨(-130801223990897851), (-130757524804558897)⟩, true⟩

def words07 : List Nat := [371285214251865566, 371285214281653395, 371285216060839489, 371285216507442026, 371285216800195750, 371285217093112761, 371285217370928109, 371285217371449930, 371285214812957442, 371285215267081471]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 16970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 16900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491974988905480, 362491978798278154⟩, ⟨(-114686816204873992), (-114643038347503928)⟩, true⟩

def words08 : List Nat := [371285219186034542, 371285220227935577, 371285220585519881, 371285220943239946, 371285222100686118, 371285222101259412, 371285225236122369, 371285228535307840, 371285231120380118, 371285231518050534]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 16980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 16900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362570018843440212, 362570022657520727⟩, ⟨(-1441027768470744969), (-1440983910604143067)⟩, true⟩

def words09 : List Nat := [371285234183565531, 371285236849046067, 371285242975509516, 371285245461287235, 371285246791005813, 371285248120731601, 371285251876687971, 371285253910732533, 371285258897482936, 371285263883883639]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 16990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 16900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 16900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk169
