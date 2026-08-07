import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk389

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488634365954209, 362488655790039345⟩, ⟨(-134870649013390487), (-134307468737976705)⟩, true⟩

def state01 : KState := ⟨⟨362469338632331067, 362469360067882787⟩, ⟨615808771369641664, 616372397754555450⟩, true⟩

def words00 : List Nat := [371285203334082376, 371285203335355184, 371285202650045454, 371285202625816527, 371285202735258975, 371285202736553912, 371285202335924830, 371285201810344391, 371285201284289875, 371285201044437775]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 38900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 38900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362465232601943497, 362465254048989706⟩, ⟨775633657433709687, 776197731125243027⟩, true⟩

def words01 : List Nat := [371285200804881264, 371285200972962283, 371285200973933080, 371285200955334419, 371285200056990915, 371285199313905375, 371285198570197079, 371285198486875157, 371285197975454104, 371285197464486244]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 38910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 38900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477294075499028, 362477315533933845⟩, ⟨306293227141282097, 306857744136367419⟩, true⟩

def words02 : List Nat := [371285197100343847, 371285197101752855, 371285197567782364, 371285198131575669, 371285198586819475, 371285198588092880, 371285198164302324, 371285197940818435, 371285197827606724, 371285197828928358]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 38920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 38900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481928887016882, 362481950357040972⟩, ⟨125906272053979553, 126471240277493769⟩, true⟩

def words03 : List Nat := [371285197627414329, 371285197417564314, 371285197655429920, 371285197868896748, 371285198192860059, 371285198517301922, 371285198841202157, 371285198842475948, 371285198287882262, 371285198206046558]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 38930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 38900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362451987745226322, 362452009226609723⟩, ⟨1291952080722073050, 1292517491335920676⟩, true⟩

def words04 : List Nat := [371285198312230100, 371285198313504164, 371285197624995157, 371285196936684395, 371285196247903923, 371285195760083604, 371285194942135814, 371285194376372109, 371285193810188785, 371285193244359041]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 38940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 38900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486967834905275, 362486989327805234⟩, ⟨(-70740657071442533), (-70174797828726997)⟩, true⟩

def words05 : List Nat := [371285192393287059, 371285191878927516, 371285191506676770, 371285191507951158, 371285190774099733, 371285189891188670, 371285189007816700, 371285188690261774, 371285188125180634, 371285188172859809]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 38950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 38900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468791887617019, 362468813392038630⟩, ⟨637519417451052423, 638085725635726009⟩, true⟩

def words06 : List Nat := [371285188173827583, 371285188155551747, 371285188070743574, 371285188304989232, 371285188738935536, 371285188740210285, 371285188297159121, 371285187855060751, 371285187412472744, 371285187159696719]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 38960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 38900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362462108568642069, 362462130084531704⟩, ⟨898129558318710805, 898696313469596393⟩, true⟩

def words07 : List Nat := [371285186978256583, 371285187217463380, 371285187331245172, 371285187332526188, 371285186817893722, 371285186502290086, 371285186526707746, 371285186527982784, 371285185993049792, 371285185402989108]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 38970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 38900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469934871679603, 362469956398998542⟩, ⟨593035648718308052, 593602849441182298⟩, true⟩

def words08 : List Nat := [371285184812406589, 371285184635276529, 371285184174230320, 371285183985212224, 371285183795787931, 371285183479884432, 371285182361569144, 371285181679035603, 371285180995872711, 371285180888596931]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 38980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 38900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479848804043960, 362479870342990692⟩, ⟨206456646487285125, 207024300635958893⟩, true⟩

def words09 : List Nat := [371285180499089385, 371285180055269526, 371285179822955836, 371285179824361280, 371285179746518722, 371285179697611723, 371285179648313949, 371285179471575431, 371285178792905649, 371285178658391615]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 38990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 38900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 38900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk389
