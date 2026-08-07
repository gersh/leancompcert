import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk711

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362469246710549659, 362469321825069604⟩, ⟨1130134970977546319, 1133741782935941657⟩, true⟩

def state01 : KState := ⟨⟨362469361591142010, 362469436727365724⟩, ⟨1121972663490784065, 1125581018698790089⟩, true⟩

def words00 : List Nat := [371285267337797403, 371285267281454737, 371285266990339888, 371285266693351083, 371285266395384174, 371285266158452200, 371285265849602079, 371285265719421456, 371285265588458587, 371285265457765089]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 71100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 71100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480514565875306, 362480589724186688⟩, ⟨328794571118664928, 332404497090966796⟩, true⟩

def words01 : List Nat := [371285265236831588, 371285265105646480, 371285264973209225, 371285264924307344, 371285264677533436, 371285264371908419, 371285264065322260, 371285263902541069, 371285263641094663, 371285263578195279]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 71110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 71100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473896711225333, 362473971891497604⟩, ⟨799430299230489328, 803041787176246404⟩, true⟩

def words02 : List Nat := [371285263514300530, 371285263437537087, 371285263128871239, 371285262951905710, 371285262773768787, 371285262649402241, 371285262381251603, 371285262077950780, 371285261773637661, 371285261667782945]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 71120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 71100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362460300626153071, 362460375828365518⟩, ⟨1766678420330671476, 1770291468989306868⟩, true⟩

def words03 : List Nat := [371285261530730123, 371285261553364508, 371285261572945808, 371285261575426193, 371285261430278683, 371285261311369369, 371285261191128785, 371285261122394570, 371285260789860275, 371285260442773577]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 71130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 71100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362466411513499427, 362466486737560763⟩, ⟨1331950113197177427, 1335564716294607391⟩, true⟩

def words04 : List Nat := [371285260094663539, 371285259830277245, 371285259476588861, 371285259321176815, 371285259165014476, 371285258969334593, 371285258509742701, 371285258248704233, 371285257986372816, 371285257850931032]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 71140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 71100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362464585098226504, 362464660344498641⟩, ⟨1461942708520418033, 1465558892030569029⟩, true⟩

def words05 : List Nat := [371285257588934114, 371285257308096261, 371285257026242198, 371285256942663495, 371285256772324835, 371285256609552553, 371285256445983729, 371285256283428779, 371285255893557680, 371285255607174732]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476483259879681, 362476558527913016⟩, ⟨615264403909582096, 618882136058253932⟩, true⟩

def words06 : List Nat := [371285255319411205, 371285255229665331, 371285255063839669, 371285254898395048, 371285254732043888, 371285254608670909, 371285254407465206, 371285254404429995, 371285254400568030, 371285254356718106]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500643387997322, 362500718678046503⟩, ⟨(-1104299344251045551), (-1100680045123219579)⟩, true⟩

def words07 : List Nat := [371285254311133291, 371285254388995906, 371285254642622144, 371285254692385846, 371285254732756089, 371285254773944661, 371285254997526345, 371285255123392292, 371285255342298142, 371285255562255447]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477583017698849, 362477658329810434⟩, ⟨537178030400208647, 540798900041747567⟩, true⟩

def words08 : List Nat := [371285255743260127, 371285255745699780, 371285255663648678, 371285255665480523, 371285255689767772, 371285255692207522, 371285255454871819, 371285255205435835, 371285254955022523, 371285254886911737]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362463741283110240, 362463816617197715⟩, ⟨1522714508451446111, 1526336942667712805⟩, true⟩

def words09 : List Nat := [371285254872163779, 371285254965152445, 371285255050523335, 371285255052963230, 371285254875421057, 371285254735906833, 371285254595180167, 371285254534618406, 371285254232118062, 371285253933808217]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk711
