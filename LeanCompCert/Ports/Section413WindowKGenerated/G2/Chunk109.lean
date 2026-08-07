import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk109

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360462450805417471, 360462451457292485⟩, ⟨1337032788253332259, 1337037603779218349⟩, true⟩

def state01 : KState := ⟨⟨360737609188116280, 360737609841242855⟩, ⟨(-1663737132610542691), (-1663732303436420165)⟩, true⟩

def words00 : List Nat := [360585104205201608, 360585094063871193, 360585093416267098, 360585097277186690, 360585097277308895, 360585095106732166, 360585098536066028, 360585101964810573, 360585113754631213, 360585127731130453]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 10900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 10900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360660236048371066, 360660236702763424⟩, ⟨(-819320003836026301), (-819315160845985891)⟩, true⟩

def words01 : List Nat := [360585137492615683, 360585147252327348, 360585156728539339, 360585172207249511, 360585182686441116, 360585193163734443, 360585199334912500, 360585200970214185, 360585207841725855, 360585214712025764]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 10910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 10900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360549523346912327, 360549524002554939⟩, ⟨390189385898052952, 390194242547249676⟩, true⟩

def words02 : List Nat := [360585226602059314, 360585234173307738, 360585235208750109, 360585236244016678, 360585236244128514, 360585231582941814, 360585231273695175, 360585230043438538, 360585228813392604, 360585223384306746]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 10920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 10900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360783083766498789, 360783084423395915⟩, ⟨(-2164310135014520988), (-2164305264647139372)⟩, true⟩

def words03 : List Nat := [360585220118530374, 360585219464579330, 360585218810709991, 360585222375921773, 360585222376045506, 360585219626923501, 360585222444745542, 360585232218685250, 360585250304003625, 360585268386045843]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 10930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 10900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360697671586711671, 360697672244878323⟩, ⟨(-1230537537679318064), (-1230532653417077746)⟩, true⟩

def words04 : List Nat := [360585279943688110, 360585283240664374, 360585291117295695, 360585298992527805, 360585301451573432, 360585301827532223, 360585301827650929, 360585296728262897, 360585294833455737, 360585305095447488]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 10940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 10900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360495697476167569, 360495698135587825⟩, ⟨982447168474470974, 982452066470148260⟩, true⟩

def words05 : List Nat := [360585320436354737, 360585335774486112, 360585346853556131, 360585349689909650, 360585349690023145, 360585346706873953, 360585349032386853, 360585349032520122, 360585346102095660, 360585337922674518]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 10950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 10900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360519636675436720, 360519637336117833⟩, ⟨720451842900241565, 720456754721125461⟩, true⟩

def words06 : List Nat := [360585329744716038, 360585330990921168, 360585338443525697, 360585345894795996, 360585345894919315, 360585345207285759, 360585336291001135, 360585328463025227, 360585320636439834, 360585312518863606]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 10960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 10900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360615700458371889, 360615701120325453⟩, ⟨(-334091178070765190), (-334086252284782998)⟩, true⟩

def words07 : List Nat := [360585306532730775, 360585294946862964, 360585283363080957, 360585282037530460, 360585282037642478, 360585281758473823, 360585281479339271, 360585277033020095, 360585274321239124, 360585277092251072]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 10970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 10900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360685767191730663, 360685767854944782⟩, ⟨(-1103906734505134273), (-1103901794871970749)⟩, true⟩

def words08 : List Nat := [360585285251296979, 360585293965247671, 360585296236237454, 360585298506826323, 360585298506938824, 360585298291021103, 360585308512676386, 360585318732496784, 360585321831612965, 360585330970687484]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 10980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 10900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360794197802866660, 360794198467343117⟩, ⟨(-2296067599726995797), (-2296062646214467129)⟩, true⟩

def words09 : List Nat := [360585344177713892, 360585357382376167, 360585378818277448, 360585397013225818, 360585408159897961, 360585419304553417, 360585430156301695, 360585446521807754, 360585465499366025, 360585484473504879]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 10990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 10900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 10900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk109
