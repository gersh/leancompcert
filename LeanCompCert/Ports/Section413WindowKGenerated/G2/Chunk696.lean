import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk696

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580578431421376, 360580609638345929⟩, ⟨142641324438164580, 144108443259625096⟩, true⟩

def state01 : KState := ⟨⟨360575371159004309, 360575402375218217⟩, ⟨505034719325729298, 506502484733447746⟩, true⟩

def words00 : List Nat := [360582680133018211, 360582680049422152, 360582679906544261, 360582679660845674, 360582679414993664, 360582679117867114, 360582678925553530, 360582678872812241, 360582678819941240, 360582678664325148]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 69600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 69600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589319594744861, 360589350820257235⟩, ⟨(-465988041675686214), (-464519628957180748)⟩, true⟩

def words01 : List Nat := [360582678621550589, 360582678683591081, 360582678893124559, 360582678896682849, 360582678897623189, 360582678701870095, 360582678505932273, 360582678507299089, 360582678603940298, 360582678700796768]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 69610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 69600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584955220028521, 360584986454940070⟩, ⟨(-162157965170996827), (-160688898035833695)⟩, true⟩

def words02 : List Nat := [360582678701676203, 360582678665593732, 360582678809828897, 360582678985495358, 360582679100998180, 360582679101984427, 360582679093915847, 360582678983146257, 360582678872201353, 360582678734269165]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 69620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 69600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360563142210901626, 360563173455084988⟩, ⟨1356868017850726221, 1358337730629695367⟩, true⟩

def words03 : List Nat := [360582678937824558, 360582679141565442, 360582679240256300, 360582679241242408, 360582679223865635, 360582679108101407, 360582679033587646, 360582679034573313, 360582678871009615, 360582678591940671]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 69630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 69600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569672982900146, 360569704236402302⟩, ⟨901961399336218190, 903431761121594524⟩, true⟩

def words04 : List Nat := [360582678312665709, 360582677967329229, 360582677744034267, 360582677517121464, 360582677290137340, 360582676887208280, 360582676341003558, 360582675962386937, 360582675583494201, 360582675259533984]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 69640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 69600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360572621232788560, 360572652495688620⟩, ⟨696616188002824764, 698087204395889226⟩, true⟩

def words05 : List Nat := [360582675074192069, 360582674769461662, 360582674464544693, 360582674414642787, 360582674415468012, 360582674414159479, 360582674412759716, 360582674254781571, 360582673987889358, 360582673845163152]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 69650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 69600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566824786987315, 360566856059170367⟩, ⟨1100436371897676971, 1101908034991576803⟩, true⟩

def words06 : List Nat := [360582673763722169, 360582673764708418, 360582673688044487, 360582673454332063, 360582673220448492, 360582672935408498, 360582672791338734, 360582672616719386, 360582672442005900, 360582672164165223]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 69660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 69600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360588043520499690, 360588074802008114⟩, ⟨(-378090227032862323), (-376617914195443479)⟩, true⟩

def words07 : List Nat := [360582671937965705, 360582671645625443, 360582671353005971, 360582671134799428, 360582670886893956, 360582670462500032, 360582670037929511, 360582669819086385, 360582669836656762, 360582669915249953]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 69670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 69600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360560251592225009, 360560282883118188⟩, ⟨1558445828084793706, 1559918794898174148⟩, true⟩

def words08 : List Nat := [360582669916128863, 360582669892014846, 360582669662021892, 360582669503135879, 360582669344013260, 360582668999513304, 360582668449244503, 360582667766950557, 360582667084486664, 360582666565065357]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 69680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 69600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360533986422490412, 360534017722692529⟩, ⟨3389080297405298902, 3390553913004628438⟩, true⟩

def words09 : List Nat := [360582666244678335, 360582666129802728, 360582666014807821, 360582665770706810, 360582665320813444, 360582664785137285, 360582664249169514, 360582663918679475, 360582663382479787, 360582662685576384]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 69690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 69600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 69600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk696
