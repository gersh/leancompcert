import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk851

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491298240048948, 362491407352603699⟩, ⟨(-526264621113603382), (-519994923834885262)⟩, true⟩

def state01 : KState := ⟨⟨362490947142040349, 362491056281265943⟩, ⟨(-496418469043927219), (-490146501938996115)⟩, true⟩

def words00 : List Nat := [371285297095349051, 371285297098313897, 371285297090485059, 371285297158171814, 371285297266623771, 371285297269632170, 371285297263689983, 371285297231675261, 371285297301251239, 371285297372288972]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 85100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 85100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483151801070172, 362483260966995029⟩, ⟨167101965922769011, 173376205531994089⟩, true⟩

def words01 : List Nat := [371285297533484492, 371285297695896956, 371285297834033000, 371285297836990129, 371285297790954881, 371285297768267222, 371285297834989279, 371285297837967909, 371285297832011509, 371285297811514907]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 85110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 85100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483680898028067, 362483790090394921⟩, ⟨122128765862649986, 128405256353246890⟩, true⟩

def words02 : List Nat := [371285297903583275, 371285297951773155, 371285298097682866, 371285298244778830, 371285298361270333, 371285298364230254, 371285298339531853, 371285298358259539, 371285298430529840, 371285298433591835]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 85120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 85100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485947408678425, 362486056628002640⟩, ⟨(-70797513847085212), (-64518728344256852)⟩, true⟩

def words03 : List Nat := [371285298418107775, 371285298404240625, 371285298510031998, 371285298583620855, 371285298698240142, 371285298814038069, 371285298907424100, 371285298910382197, 371285298828582132, 371285298841174388]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 85130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 85100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479965134086998, 362480074379762097⟩, ⟨438538621311599297, 444819650467100357⟩, true⟩

def words04 : List Nat := [371285298909194827, 371285298912152995, 371285298796491353, 371285298674574498, 371285298551497733, 371285298471898285, 371285298333195372, 371285298333553467, 371285298332904404, 371285298333378857]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 85140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 85100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488501251128915, 362488610523561192⟩, ⟨(-288379971112112922), (-282096663448366778)⟩, true⟩

def words05 : List Nat := [371285298283776696, 371285298297087807, 371285298395965034, 371285298398923545, 371285298314319276, 371285298195281680, 371285298075071420, 371285298029301264, 371285297971320113, 371285298013568962]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480297727915891, 362480407027066939⟩, ⟨410281918273023855, 416567501443256621⟩, true⟩

def words06 : List Nat := [371285298054582726, 371285298057614723, 371285298087716091, 371285298151013678, 371285298255166747, 371285298258125876, 371285298193513789, 371285298130198158, 371285298065678545, 371285298039177345]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470313766790942, 362470423092566738⟩, ⟨1260714160874014410, 1267002011807287332⟩, true⟩

def words07 : List Nat := [371285298045308951, 371285298110042606, 371285298138751071, 371285298141712071, 371285298010640152, 371285297921859898, 371285297840548080, 371285297843507570, 371285297671171239, 371285297499843180]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472342856303455, 362472452208601711⟩, ⟨1087888935558286858, 1094179045809665908⟩, true⟩

def words08 : List Nat := [371285297327229093, 371285297277663623, 371285297158121943, 371285297083180329, 371285297007277665, 371285296910407195, 371285296642233090, 371285296462677631, 371285296281630289, 371285296193175132]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474634849431966, 362474744228706400⟩, ⟨892636745691336120, 898929154175848880⟩, true⟩

def words09 : List Nat := [371285296044620898, 371285295898515873, 371285295751178058, 371285295742787091, 371285295664185144, 371285295591973542, 371285295518821636, 371285295419982798, 371285295160498455, 371285295040375131]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk851
