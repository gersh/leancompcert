import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk105

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360703094207044393, 360703094809750482⟩, ⟨(-1273394430357439001), (-1273390141005676991)⟩, true⟩

def state01 : KState := ⟨⟨360640197152422134, 360640197756327093⟩, ⟨(-612433807905432457), (-612429505959500411)⟩, true⟩

def words00 : List Nat := [360581851688990255, 360581867600096953, 360581878879459016, 360581890156686972, 360581895278515037, 360581907085894998, 360581915256867161, 360581923426306623, 360581926632888045, 360581932176842791]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 10500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 10500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360829056934244107, 360829057539352203⟩, ⟨(-2598359407954173098), (-2598355093357123782)⟩, true⟩

def words01 : List Nat := [360581941600703261, 360581951022809003, 360581969461522254, 360581988279898035, 360581999425721102, 360582010569435453, 360582024103410200, 360582042129538313, 360582065610193947, 360582089086414543]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 10510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 10500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360722313063899517, 360722313670225869⟩, ⟨(-1475993827514906658), (-1475989500095970370)⟩, true⟩

def words02 : List Nat := [360582105405122611, 360582112804199471, 360582122996818830, 360582133187538086, 360582140797364557, 360582144917506504, 360582144917621081, 360582141523854205, 360582143727049585, 360582157037418352]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 10520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 10500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360648218314870110, 360648218922397783⟩, ⟨(-695029719085583641), (-695025379010649223)⟩, true⟩

def words03 : List Nat := [360582179332465726, 360582201623303979, 360582219329981378, 360582233566182210, 360582240860001074, 360582248152467164, 360582260152541043, 360582270978416649, 360582277235452160, 360582283491318128]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 10530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 10500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360666492228307045, 360666492837042884⟩, ⟨(-887159168321520222), (-887154815506545838)⟩, true⟩

def words04 : List Nat := [360582295612117778, 360582314891568629, 360582336574265522, 360582358252873833, 360582371742704364, 360582376357946967, 360582386715868885, 360582397071865344, 360582402333070980, 360582410303111831]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 10540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 10500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360624925510115043, 360624926120069442⟩, ⟨(-448395667275026568), (-448391301598102766)⟩, true⟩

def words05 : List Nat := [360582413716446971, 360582417129149144, 360582426113157531, 360582439556192494, 360582450661890205, 360582461765507599, 360582465709981215, 360582465710109236, 360582464822423124, 360582468843145088]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 10550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 10500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360642617770836711, 360642618381998436⟩, ⟨(-635856121904532616), (-635851743472054228)⟩, true⟩

def words06 : List Nat := [360582478163721883, 360582478633129770, 360582478633245853, 360582472221088828, 360582465810124645, 360582457077586943, 360582458006157938, 360582462927843811, 360582462927958584, 360582467805565549]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 10560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 10500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360706018070358277, 360706018682729453⟩, ⟨(-1306666258527536854), (-1306661867305199116)⟩, true⟩

def words07 : List Nat := [360582472845731897, 360582477884981250, 360582488563434260, 360582496724921854, 360582497146476584, 360582497567960471, 360582497660852612, 360582503996104035, 360582515670563993, 360582527342846153]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 10570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 10500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360772192909120537, 360772193522714304⟩, ⟨(-2007735952995134907), (-2007731548831706657)⟩, true⟩

def words08 : List Nat := [360582534485114826, 360582546262616106, 360582561538575271, 360582576811688896, 360582587461388991, 360582593274045938, 360582594568180391, 360582595862084434, 360582606029760706, 360582623930718109]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 10580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 10500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360552856180456855, 360552856795262453⟩, ⟨315698461692791143, 315702878695639191⟩, true⟩

def words09 : List Nat := [360582637356423527, 360582650779616554, 360582657309070077, 360582657309198621, 360582655034695587, 360582647467359892, 360582641201790177, 360582642895467141, 360582642895581751, 360582640085705438]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 10590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 10500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 10500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk105
