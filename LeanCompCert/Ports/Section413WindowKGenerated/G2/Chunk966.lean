import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk966

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360595959857419319, 360596021533678984⟩, ⟨(-1328592192312521306), (-1324569142602081276)⟩, true⟩

def state01 : KState := ⟨⟨360594463344262255, 360594525033709632⟩, ⟨(-1183990172167624451), (-1179965848455821401)⟩, true⟩

def words00 : List Nat := [360582310029994639, 360582310264091569, 360582310431297596, 360582310598647259, 360582310731812161, 360582310918584765, 360582311073324487, 360582311228309262, 360582311329241783, 360582311457114257]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 96600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 96600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360614482286982778, 360614543989656592⟩, ⟨(-3118161170431499169), (-3114135568848175369)⟩, true⟩

def words01 : List Nat := [360582311620909327, 360582311785109831, 360582311965165720, 360582312177330326, 360582312303983081, 360582312430733951, 360582312637654099, 360582312898271304, 360582313232990707, 360582313568021046]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 96610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 96600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593550136903877, 360593611852951838⟩, ⟨(-1095684019562387748), (-1091657125704639198)⟩, true⟩

def words02 : List Nat := [360582313813591463, 360582313952519325, 360582314141714551, 360582314331341312, 360582314491714268, 360582314545547451, 360582314546797266, 360582314541758218, 360582314561424911, 360582314679935885]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 96620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 96600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574358903598781, 360574420632833121⟩, ⟨758906973611818557, 762935141736592745⟩, true⟩

def words03 : List Nat := [360582314874914204, 360582315070157569, 360582315210892437, 360582315305178736, 360582315306380666, 360582315299796314, 360582315348591903, 360582315349994037, 360582315323397552, 360582315243157383]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 96630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 96600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360605606007780071, 360605667750275210⟩, ⟨(-2260920553651685334), (-2256891103940690216)⟩, true⟩

def words04 : List Nat := [360582315170671257, 360582315272297413, 360582315480533514, 360582315689034838, 360582315792450200, 360582315924223455, 360582316141312315, 360582316358808501, 360582316573405916, 360582316816462413]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 96640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 96600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360597689665972412, 360597751421831721⟩, ⟨(-1495768748517668006), (-1491738007094286822)⟩, true⟩

def words05 : List Nat := [360582317005911164, 360582317195497535, 360582317431995357, 360582317728312178, 360582317965867712, 360582318203666047, 360582318345272895, 360582318422597996, 360582318583394436, 360582318744670361]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 96650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 96600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360610152437013726, 360610214206100487⟩, ⟨(-2700504966169064062), (-2696472946112647272)⟩, true⟩

def words06 : List Nat := [360582319012486401, 360582319244015091, 360582319393070524, 360582319542254717, 360582319663944569, 360582319839256229, 360582320121167137, 360582320403357399, 360582320618752432, 360582320908771271]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 96660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 96600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611720676029949, 360611782458346778⟩, ⟨(-2852068732337057266), (-2848035433264083210)⟩, true⟩

def words07 : List Nat := [360582321305448632, 360582321702533487, 360582322188218998, 360582322567508394, 360582322855029213, 360582323142651653, 360582323425722983, 360582323778753838, 360582324084601858, 360582324390750621]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 96670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 96600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602656090854920, 360602717886528077⟩, ⟨(-1975767409905304468), (-1971732819476781844)⟩, true⟩

def words08 : List Nat := [360582324608509459, 360582324719768405, 360582324918568271, 360582325117802951, 360582325274470260, 360582325373033684, 360582325417526269, 360582325462158160, 360582325571135838, 360582325783649042]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 96680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 96600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360591999052888004, 360592060861787709⟩, ⟨(-945315507766509749), (-941279638396609821)⟩, true⟩

def words09 : List Nat := [360582325959508595, 360582326135613154, 360582326252337634, 360582326337631976, 360582326383836961, 360582326430431845, 360582326583546711, 360582326739409036, 360582326841322069, 360582326943437366]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 96690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 96600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 96600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk966
