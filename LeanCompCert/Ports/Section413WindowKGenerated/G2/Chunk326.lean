import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk326

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587752332805967, 360587758769956058⟩, ⟨(-210036214399271721), (-209894317729836443)⟩, true⟩

def state01 : KState := ⟨⟨360620243723924097, 360620250165214073⟩, ⟨(-1269745895464268150), (-1269603863814311366)⟩, true⟩

def words00 : List Nat := [360581320491832674, 360581320219087614, 360581319007426302, 360581318733915886, 360581318460300957, 360581317948954073, 360581317882371951, 360581317343700633, 360581317203546669, 360581318397901991]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 32600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 32600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360563296616493487, 360563303061884730⟩, ⟨587758306676600561, 587900472089393675⟩, true⟩

def words01 : List Nat := [360581320529590458, 360581322661231686, 360581324068109618, 360581325058965419, 360581325412905882, 360581325766942105, 360581326329870840, 360581326330305985, 360581326313889817, 360581325761826159]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 32610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 32600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360601636713737122, 360601643163233706⟩, ⟨(-663082327773450071), (-662940028424240929)⟩, true⟩

def words02 : List Nat := [360581325594393778, 360581326454701880, 360581327114599732, 360581327774538654, 360581327774944288, 360581327614311111, 360581327326439955, 360581326758784561, 360581326275609220, 360581326898686980]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 32620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 32600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592408111979105, 360592414565619547⟩, ⟨(-361836543438812413), (-361694108855254685)⟩, true⟩

def words03 : List Nat := [360581326970853833, 360581327043063750, 360581328051797453, 360581329863313705, 360581331276639143, 360581332689949079, 360581333268662486, 360581333269097917, 360581333250512556, 360581333590500671]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 32630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 32600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589531697218364, 360589538154964723⟩, ⟨(-268072930677769366), (-267930362056427554)⟩, true⟩

def words04 : List Nat := [360581333904553282, 360581333904989671, 360581333830651771, 360581333136634105, 360581332442588009, 360581331510988021, 360581331531239519, 360581332009480127, 360581332017850262, 360581332269630234]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 32640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 32600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360625985695178136, 360625992157034953⟩, ⟨(-1458422383830050034), (-1458279680981624198)⟩, true⟩

def words05 : List Nat := [360581333213056807, 360581334156557348, 360581336035202665, 360581337447160342, 360581337968425392, 360581338489687778, 360581339239155342, 360581340462025460, 360581341829547856, 360581343197083280]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 32650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 32600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587928133875294, 360587934599890426⟩, ⟨(-215337783025978601), (-215194944346983321)⟩, true⟩

def words06 : List Nat := [360581343979023000, 360581344795059554, 360581346290236347, 360581347785449003, 360581348872404773, 360581349024611604, 360581349024999906, 360581348708397515, 360581348391739022, 360581347873302719]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 32660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 32600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360551749285368674, 360551755755484715⟩, ⟨966960531160062442, 967103503836565702⟩, true⟩

def words07 : List Nat := [360581348603859060, 360581349334453805, 360581349596507543, 360581349801329331, 360581349801694641, 360581349764272188, 360581350225587960, 360581350226023885, 360581349791075158, 360581348885957071]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 32670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 32600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586355565628845, 360586362039865039⟩, ⟨(-164329192584712817), (-164186085240947165)⟩, true⟩

def words08 : List Nat := [360581347980797226, 360581347221255209, 360581347066657156, 360581346402029497, 360581345737408523, 360581344273826038, 360581342226754554, 360581341113125428, 360581339999432606, 360581339676363129]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 32680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 32600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360553165428873917, 360553171907261784⟩, ⟨920898253368492709, 921041496451085255⟩, true⟩

def words09 : List Nat := [360581339676752719, 360581339174231190, 360581339101639136, 360581340004408054, 360581340391436791, 360581340778511391, 360581340778910722, 360581340443429523, 360581339174767793, 360581338313881084]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 32690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 32600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 32600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk326
