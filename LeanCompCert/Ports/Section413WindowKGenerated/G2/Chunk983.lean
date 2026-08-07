import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk983

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582945507313735, 360583009459635061⟩, ⟨(-60460706259439890), (-56215848425965284)⟩, true⟩

def state01 : KState := ⟨⟨360584049471015006, 360584113436956073⟩, ⟨(-169067581306057158), (-164821384585445284)⟩, true⟩

def words00 : List Nat := [360582437586296157, 360582437512037379, 360582437389164494, 360582437355086018, 360582437320629482, 360582437260146800, 360582437212970497, 360582437085275831, 360582436957285684, 360582436906511002]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 98300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 98300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360570476814528755, 360570540793911211⟩, ⟨1165319613214907378, 1169567131427505520⟩, true⟩

def words01 : List Nat := [360582436959888982, 360582437013536577, 360582437015162588, 360582437016590805, 360582436915038510, 360582436736964068, 360582436558458902, 360582436483630250, 360582436429404340, 360582436309893997]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 98310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 98300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360588875939545859, 360588939932426195⟩, ⟨(-643694587660449015), (-639445742270437515)⟩, true⟩

def words02 : List Nat := [360582436190061910, 360582436236991308, 360582436404454307, 360582436572188265, 360582436646767837, 360582436648196210, 360582436734788359, 360582436830771461, 360582436872447803, 360582436940060915]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 98320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 98300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583015172952658, 360583079179434237⟩, ⟨(-67359456003586677), (-63109273137117701)⟩, true⟩

def words03 : List Nat := [360582436951061238, 360582436962225417, 360582437055660716, 360582437203252119, 360582437310095388, 360582437417194467, 360582437472258127, 360582437473686674, 360582437432083207, 360582437440249796]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 98330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 98300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581317218233640, 360581381238182939⟩, ⟨99562770098589413, 103814277446769375⟩, true⟩

def words04 : List Nat := [360582437514168703, 360582437515597298, 360582437486596164, 360582437373308860, 360582437259796793, 360582437061949301, 360582436931154761, 360582436903969999, 360582436876627753, 360582436797689262]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 98340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 98300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360584098395677653, 360584162429102242⟩, ⟨(-174016753122671063), (-169763920412337143)⟩, true⟩

def words05 : List Nat := [360582436793207880, 360582436799885590, 360582436877043936, 360582436878472717, 360582436852739456, 360582436738978828, 360582436624966589, 360582436508914371, 360582436482925794, 360582436501952129]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 98350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 98300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585101191959106, 360585165239002588⟩, ⟨(-272731718366158521), (-268477546034558281)⟩, true⟩

def words06 : List Nat := [360582436503238222, 360582436472221717, 360582436483229116, 360582436494680114, 360582436495876021, 360582436466336847, 360582436356814835, 360582436195655541, 360582436034223953, 360582436004309086]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 98360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 98300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360563231119765594, 360563295180282570⟩, ⟨1878691647543283300, 1882947145330557826⟩, true⟩

def words07 : List Nat := [360582436005492187, 360582435964017128, 360582435922395645, 360582435800826395, 360582435602367075, 360582435376138552, 360582435149494851, 360582435026416741, 360582434905221532, 360582434712152163]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 98370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 98300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586443157718252, 360586507231723815⟩, ⟨(-405026542826662868), (-400769717964432144)⟩, true⟩

def words08 : List Nat := [360582434518762427, 360582434408614677, 360582434371749532, 360582434384023407, 360582434385364563, 360582434299108974, 360582434109596385, 360582434023761666, 360582433953305686, 360582433996184341]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 98380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 98300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571409428534579, 360571473516171846⟩, ⟨1074262394523695857, 1078520560676287471⟩, true⟩

def words09 : List Nat := [360582433997457702, 360582433988551952, 360582434043008747, 360582434176998199, 360582434244300297, 360582434311830067, 360582434313122787, 360582434308533966, 360582434200731112, 360582434090975467]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 98390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 98300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 98300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk983
