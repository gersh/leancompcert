import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk101

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362576153972277652, 362576155257641384⟩, ⟨(-929011931947636936), (-929003142402267406)⟩, true⟩

def state01 : KState := ⟨⟨362457537229050644, 362457538517084745⟩, ⟨269358704051747221, 269367520581607397⟩, true⟩

def words00 : List Nat := [371284190692476534, 371284190692772257, 371284188082939841, 371284191673663728, 371284197198496181, 371284197198792232, 371284192141701284, 371284187199840102, 371284182258835153, 371284182188754539]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 10100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 10100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362395977364933335, 362395978655635929⟩, ⟨892580136527201202, 892588980049079278⟩, true⟩

def words01 : List Nat := [371284186696866320, 371284193838806414, 371284200894689471, 371284200894986914, 371284198765073138, 371284195456103781, 371284196504072416, 371284196504368591, 371284187863723231, 371284179147735641]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 10110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 10100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362394671870939545, 362394673164297569⟩, ⟨906329301211511252, 906338171620042196⟩, true⟩

def words02 : List Nat := [371284170433334832, 371284168609204039, 371284165841875915, 371284168486541486, 371284169582400314, 371284169582696836, 371284159800129114, 371284153183209289, 371284146567443466, 371284143862384444]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 10120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 10100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362446077613097859, 362446078909155568⟩, ⟨385333516861404053, 385342414631482957⟩, true⟩

def words03 : List Nat := [371284135031229336, 371284124340928663, 371284113652620136, 371284112697859067, 371284106869849587, 371284103937123333, 371284101004868474, 371284098340742093, 371284084867428791, 371284081119671494]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 10130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 10100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473598749985723, 362473600048693734⟩, ⟨106284719165088644, 106293643822858202⟩, true⟩

def words04 : List Nat := [371284083346665332, 371284083346964171, 371284080788932077, 371284076112736344, 371284071437345623, 371284069654535275, 371284067218918768, 371284070164162723, 371284072328560093, 371284072328873326]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 10140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 10100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362541659291139502, 362541660592535639⟩, ⟨(-584884512555331576), (-584875560599318614)⟩, true⟩

def words05 : List Nat := [371284079967718299, 371284088636664143, 371284099759461372, 371284099759758664, 371284097973893974, 371284094836980723, 371284092456354333, 371284092456681659, 371284094100013314, 371284099765786371]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 10150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 10100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362548213005117534, 362548214309202129⟩, ⟨(-651919521340433140), (-651910542056164938)⟩, true⟩

def words06 : List Nat := [371284105551312723, 371284105551610205, 371284101029448792, 371284103609913852, 371284108260179980, 371284108260480153, 371284107091766431, 371284105829618434, 371284112977291216, 371284119279995939]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 10160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 10100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362464248792473568, 362464250099240126⟩, ⟨202508271212022478, 202517277785675046⟩, true⟩

def words07 : List Nat := [371284129471861503, 371284139661837349, 371284149759221147, 371284149759518960, 371284146997623635, 371284143816825244, 371284147110611386, 371284147110914321, 371284145695508320, 371284143741458759]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 10170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 10100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362539517241594234, 362539518551027261⟩, ⟨(-563773941031335029), (-563764907299235157)⟩, true⟩

def words08 : List Nat := [371284149483491650, 371284152421491231, 371284161141975510, 371284169860870386, 371284175368873196, 371284175369173325, 371284177091322819, 371284181749285628, 371284193240875816, 371284198670024491]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 10180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 10100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493513709451465, 362493515021610444⟩, ⟨(-94310225939189840), (-94301164416266484)⟩, true⟩

def words09 : List Nat := [371284203917039689, 371284209163136013, 371284224034749702, 371284234157259788, 371284247133932299, 371284260108170333, 371284270904375226, 371284270904673750, 371284269809040203, 371284270715717271]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 10190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 10100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 10100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk101
