import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk696A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk696A
