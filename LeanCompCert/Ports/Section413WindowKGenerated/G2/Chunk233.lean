import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk233

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360730332996294532, 360730336190292628⟩, ⟨(-3482216213629149346), (-3482165864631227596)⟩, true⟩

def state01 : KState := ⟨⟨360630799349229427, 360630802546116381⟩, ⟨(-1162819015319935080), (-1162768598997653860)⟩, true⟩

def words00 : List Nat := [360580898908434718, 360580903244418708, 360580907514918269, 360580911785135439, 360580915137790327, 360580917427927665, 360580918430999871, 360580919434018283, 360580919722982526, 360580921863219996]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 23300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 23300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360542600263063558, 360542603462799696⟩, ⟨893792372814279507, 893842855565477263⟩, true⟩

def words01 : List Nat := [360580925839693288, 360580929815883494, 360580932662663241, 360580933683447509, 360580934232783504, 360580934782152550, 360580935267066146, 360580935267369093, 360580934559682440, 360580932916297358]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 23310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 23300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360659140199804322, 360659143402398932⟩, ⟨(-1824379217768472111), (-1824328668343668197)⟩, true⟩

def words02 : List Nat := [360580931464518503, 360580933005374197, 360580935898648560, 360580938791738621, 360580940105135037, 360580940128228605, 360580941985275299, 360580943842254482, 360580946716772856, 360580950068707978]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 23320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 23300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360679201700489892, 360679204905973627⟩, ⟨(-2292705392126648191), (-2292654775283830021)⟩, true⟩

def words03 : List Nat := [360580951628110521, 360580953187406642, 360580956579490776, 360580960889247103, 360580964154737253, 360580967419995683, 360580969751718809, 360580972128687978, 360580976337707019, 360580980546465302]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 23330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 23300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360652801057442238, 360652804265782120⟩, ⟨(-1676418889086727982), (-1676368205567186806)⟩, true⟩

def words04 : List Nat := [360580985343475372, 360580989879903064, 360580993351094890, 360580996822022142, 360580998558652679, 360581001224724281, 360581004909387436, 360581008593794063, 360581011194565650, 360581014269397932]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 23340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 23300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360656381605566819, 360656384816774090⟩, ⟨(-1760132827753042607), (-1760082077265667903)⟩, true⟩

def words05 : List Nat := [360581018118705473, 360581021967776955, 360581025969848618, 360581028153461521, 360581028767420388, 360581029381347525, 360581031824487005, 360581035611309781, 360581038837125057, 360581042062728216]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 23350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 23300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360663832321960432, 360663835536058796⟩, ⟨(-1934719992992336295), (-1934669174954887455)⟩, true⟩

def words06 : List Nat := [360581044094787253, 360581044309241859, 360581045741028340, 360581047172785987, 360581048136128308, 360581049143041265, 360581049230258392, 360581049317501499, 360581051232119690, 360581054774647009]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 23360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 23300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360610732301165349, 360610735518128195⟩, ⟨(-693237590059090114), (-693186705064492506)⟩, true⟩

def words07 : List Nat := [360581060144055059, 360581065513061547, 360581069439037136, 360581073812526436, 360581076584265042, 360581079355843934, 360581083358178928, 360581085545123958, 360581086813571435, 360581088081959319]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 23370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 23300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360658311242138104, 360658314461967678⟩, ⟨(-1805715483970938840), (-1805664531937854654)⟩, true⟩

def words08 : List Nat := [360581090605473316, 360581094073449036, 360581098746059433, 360581103418328279, 360581106534761496, 360581109389158959, 360581111441173216, 360581113493095256, 360581116320056910, 360581119620706601]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 23380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 23300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360652249958031828, 360652253180759632⟩, ⟨(-1663903426764074343), (-1663852406927291023)⟩, true⟩

def words09 : List Nat := [360581121776704973, 360581123932550162, 360581127366824108, 360581132253165027, 360581136672656585, 360581141091819826, 360581144120836263, 360581145337650502, 360581148376693346, 360581151415581764]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 23390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 23300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 23300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk233
