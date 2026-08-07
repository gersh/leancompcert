import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk417

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360614163712422191, 360614174459767779⟩, ⟨(-1323772880863829251), (-1323469997626124205)⟩, true⟩

def state01 : KState := ⟨⟨360607504666845411, 360607515419532408⟩, ⟨(-1046227411595593896), (-1045924305594521642)⟩, true⟩

def words00 : List Nat := [360582437874236704, 360582438117439791, 360582438117945121, 360582438073785292, 360582438029533571, 360582437846238446, 360582438431449684, 360582439016741335, 360582439314759193, 360582439916533331]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 41700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 41700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360618882505731812, 360618893263780502⟩, ⟨(-1520988883803894342), (-1520685554140447390)⟩, true⟩

def words01 : List Nat := [360582440907454178, 360582441898497730, 360582442702787851, 360582442935661442, 360582442936190003, 360582442665837960, 360582442395392581, 360582442591468099, 360582443465624721, 360582444339877901]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 41710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 41700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604930248863036, 360604941012313746⟩, ⟨(-939048444135486971), (-938744889073488817)⟩, true⟩

def words02 : List Nat := [360582444927062429, 360582445257188082, 360582445675100782, 360582446093163755, 360582446367088077, 360582446367655920, 360582446301267214, 360582445785980077, 360582445327765533, 360582445867479607]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 41720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 41700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360602684452407242, 360602695221198687⟩, ⟨(-845239913288149937), (-844936135330090997)⟩, true⟩

def words03 : List Nat := [360582446708359121, 360582447549306542, 360582448100360614, 360582448968215083, 360582449495509954, 360582450022928998, 360582451122920569, 360582451895269424, 360582452380761402, 360582452866311883]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 41730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 41700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360601235827227394, 360601246601386077⟩, ⟨(-784887342788436491), (-784583340776398417)⟩, true⟩

def words04 : List Nat := [360582453179003344, 360582453783331275, 360582454337057242, 360582454890862161, 360582454891389888, 360582454849122416, 360582454236198961, 360582454074354663, 360582454185449841, 360582454636145092]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 41740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 41700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360586152597062000, 360586163376630505⟩, ⟨(-155090862918151652), (-154786635019242116)⟩, true⟩

def words05 : List Nat := [360582454797380367, 360582454958666675, 360582455478649684, 360582456284692746, 360582456695189788, 360582457105758095, 360582457193091588, 360582457193659473, 360582456799467544, 360582456888878315]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 41750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 41700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601984214116625, 360601994999041447⟩, ⟨(-816162871553705682), (-815858419948237682)⟩, true⟩

def words06 : List Nat := [360582457550213226, 360582458440773363, 360582459044717676, 360582459648695170, 360582460106178808, 360582460849455887, 360582461680356575, 360582462511323897, 360582462836137379, 360582463304326257]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 41760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 41700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360651243673438123, 360651254463720609⟩, ⟨(-2874036391446105734), (-2873731716023962946)⟩, true⟩

def words07 : List Nat := [360582464344172188, 360582465384134807, 360582466756170120, 360582467558436258, 360582467858623888, 360582468158850617, 360582469030589012, 360582470343473869, 360582471990274276, 360582473637124215]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 41770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 41700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608853005679629, 360608863801380738⟩, ⟨(-1102887930972844858), (-1102583029134389762)⟩, true⟩

def words08 : List Nat := [360582474934265249, 360582476064509643, 360582477043625050, 360582478022851900, 360582478748580232, 360582479288427373, 360582479539488707, 360582479790595741, 360582479904355821, 360582480536344382]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 41780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 41700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360530181825689547, 360530192626741407⟩, ⟨2185276285655058605, 2185581411128186481⟩, true⟩

def words09 : List Nat := [360582481338876022, 360582482141477327, 360582482657814325, 360582482658382682, 360582482605477442, 360582482239495847, 360582481873366748, 360582481478114175, 360582480513683529, 360582479263371268]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 41790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 41700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 41700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk417
