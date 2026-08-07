import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk666

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493289226657337, 362493354798234726⟩, ⟨(-525764992971346348), (-522815465412775522)⟩, true⟩

def state01 : KState := ⟨⟨362482417641027121, 362482483232811031⟩, ⟨198363231942371012, 201314105361792904⟩, true⟩

def words00 : List Nat := [371285505178614128, 371285505223639731, 371285505257509999, 371285505292125338, 371285505297367854, 371285505299877798, 371285505310592362, 371285505410694026, 371285505510978365, 371285505513329899]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 66600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 66600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500653786063875, 362500719398392672⟩, ⟨(-1016409753419281012), (-1013457511400800324)⟩, true⟩

def words01 : List Nat := [371285505610992515, 371285505755235617, 371285506066147165, 371285506145276714, 371285506187719133, 371285506230904661, 371285506498177199, 371285506654512292, 371285506884432740, 371285507115307747]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 66610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 66600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486747690880511, 362486813323702278⟩, ⟨(-89983550146736696), (-87029942780022026)⟩, true⟩

def words02 : List Nat := [371285507338026327, 371285507340298659, 371285507326965099, 371285507393911968, 371285507474469448, 371285507476781475, 371285507369860662, 371285507223884885, 371285507153576469, 371285507175771435]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 66620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 66600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479444751573502, 362479510404926966⟩, ⟨396675230851378435, 399630206345822411⟩, true⟩

def words03 : List Nat := [371285507359810474, 371285507544786570, 371285507678856771, 371285507681129517, 371285507515086102, 371285507419226469, 371285507399717030, 371285507402016213, 371285507344116347, 371285507256762888]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 66630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 66600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487641907683457, 362487707581344491⟩, ⟨(-149544136268514286), (-146587807372013424)⟩, true⟩

def words04 : List Nat := [371285507279108689, 371285507302902783, 371285507550583601, 371285507799161092, 371285508010474714, 371285508012748678, 371285508016074214, 371285508066818043, 371285508212033552, 371285508247390432]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 66640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 66600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362494209991750908, 362494275686114741⟩, ⟨(-587306871727425864), (-584349162885851114)⟩, true⟩

def words05 : List Nat := [371285508280967384, 371285508315287251, 371285508573497578, 371285508762746963, 371285509020031643, 371285509278211197, 371285509506804991, 371285509509078512, 371285509569250812, 371285509703562937]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 66650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 66600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480697591236754, 362480763305851870⟩, ⟨313476472067644718, 316435530965258364⟩, true⟩

def words06 : List Nat := [371285509905751338, 371285509908025151, 371285509810632560, 371285509711144828, 371285509610757550, 371285509570144636, 371285509487790422, 371285509547151430, 371285509599146935, 371285509601501567]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 66660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 66600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362492466728070457, 362492532463264771⟩, ⟨(-471249648961347590), (-468289217945443442)⟩, true⟩

def words07 : List Nat := [371285509531869707, 371285509509033835, 371285509652465522, 371285509654747836, 371285509643025790, 371285509574835350, 371285509517964845, 371285509520471179, 371285509527006518, 371285509634903687]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 66670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 66600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487712391064455, 362487778146830546⟩, ⟨(-154196891393442394), (-151235088549000728)⟩, true⟩

def words08 : List Nat := [371285509741570846, 371285509743900829, 371285509931104057, 371285510138915315, 371285510414596032, 371285510416870894, 371285510393140979, 371285510370517441, 371285510411569331, 371285510448212307]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 66680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 66600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473116617121121, 362473182393336773⟩, ⟨819307916796290855, 822271083526650167⟩, true⟩

def words09 : List Nat := [371285510626878728, 371285510806440526, 371285510929672607, 371285510931947657, 371285510755636984, 371285510649533316, 371285510657755049, 371285510660030162, 371285510477924361, 371285510295638522]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 66690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 66600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 66600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk666
