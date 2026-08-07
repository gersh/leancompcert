import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk692

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588839256983677, 360588870092031935⟩, ⟨(-424886686982030133), (-423445376430976061)⟩, true⟩

def state01 : KState := ⟨⟨360574170250856976, 360574201095247217⟩, ⟨590245312732964850, 591687269795172586⟩, true⟩

def words00 : List Nat := [360582751028506506, 360582750956555339, 360582751032533115, 360582751175373742, 360582751265591783, 360582751266570902, 360582751148290306, 360582750851475415, 360582750554495138, 360582750253891852]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 69200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 69200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360546871508121873, 360546902361732357⟩, ⟨2479785402175361227, 2481227997417954961⟩, true⟩

def words01 : List Nat := [360582750157013391, 360582750183855891, 360582750184728560, 360582750107460829, 360582749821519265, 360582749459323492, 360582749096833926, 360582748826751582, 360582748414510457, 360582747897667318]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 69210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 69200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360563947239127743, 360563978102001330⟩, ⟨1297662568026903431, 1299105804505537471⟩, true⟩

def words02 : List Nat := [360582747380617362, 360582747072085098, 360582746877388024, 360582746521401731, 360582746165352601, 360582745627701107, 360582744881424677, 360582744256172972, 360582743630641110, 360582743172122745]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 69220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 69200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573256652220974, 360573287524419153⟩, ⟨653109798640191663, 654553680706445527⟩, true⟩

def words03 : List Nat := [360582742901945852, 360582742513394731, 360582742124667389, 360582741944383147, 360582741921007118, 360582741806415862, 360582741691742922, 360582741407520527, 360582741063657701, 360582740928242181]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 69230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 69200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567308597308157, 360567339478727118⟩, ⟨1064936663626685021, 1066381184187150063⟩, true⟩

def words04 : List Nat := [360582740792507580, 360582740728225137, 360582740510688572, 360582740189260824, 360582739867671252, 360582739409704049, 360582739055884146, 360582738910326500, 360582738764666765, 360582738484996969]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 69240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 69200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360590389937810667, 360590420828497497⟩, ⟨(-533709925435195563), (-532264763031100389)⟩, true⟩

def words05 : List Nat := [360582738263441917, 360582737955460852, 360582737647201538, 360582737437451389, 360582737102402694, 360582736595198368, 360582736087814584, 360582735788768630, 360582735803471638, 360582735915443526]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 69250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 69200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576877083371150, 360576907983384480⟩, ⟨402137080066412028, 403582888470950612⟩, true⟩

def words06 : List Nat := [360582735923287965, 360582735924268014, 360582735730579936, 360582735738430786, 360582735739265481, 360582735601831784, 360582735331198184, 360582734902162767, 360582734472952227, 360582734212465915]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 69260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 69200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360556454459758693, 360556485369019075⟩, ⟨1816962708053383058, 1818409157046666126⟩, true⟩

def words07 : List Nat := [360582734190053231, 360582734251951036, 360582734252832999, 360582734189943846, 360582734037012480, 360582733750649452, 360582733464009556, 360582733207330065, 360582732992205696, 360582732614357509]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 69270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 69200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596314505530851, 360596345424043549⟩, ⟨(-944751046308155216), (-943303956269278354)⟩, true⟩

def words08 : List Nat := [360582732236298886, 360582731972312426, 360582731814014199, 360582731810985497, 360582731807881588, 360582731626448620, 360582731495984130, 360582731516400361, 360582731568841375, 360582731766335200]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 69280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 69200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571011916776395, 360571042844650610⟩, ⟨808596982722615583, 810044721464778893⟩, true⟩

def words09 : List Nat := [360582731859170063, 360582731952103538, 360582731971460995, 360582732095929015, 360582732167879663, 360582732239988308, 360582732240862097, 360582732209111653, 360582731969187132, 360582731801670304]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 69290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 69200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 69200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk692
