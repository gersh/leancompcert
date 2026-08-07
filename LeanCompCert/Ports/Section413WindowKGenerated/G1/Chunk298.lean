import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk298

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362431095029721174, 362431107327803278⟩, ⟨1624681201822984218, 1624928926101249992⟩, true⟩

def state01 : KState := ⟨⟨362470278609065805, 362470290915697988⟩, ⟨456867573932497683, 457115553046453363⟩, true⟩

def words00 : List Nat := [371285633315034413, 371285632203805412, 371285630526315708, 371285629972362634, 371285629418159237, 371285628671980873, 371285626988661096, 371285626152002171, 371285625314883470, 371285625218047752]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 29800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 29800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471058978244397, 362471071293568144⟩, ⟨433576717494963006, 433824955748967948⟩, true⟩

def words01 : List Nat := [371285624704379906, 371285624148616023, 371285623592521330, 371285623509236771, 371285622860302280, 371285622415113460, 371285621969631723, 371285621510139115, 371285619900839532, 371285619414149934]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 29810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 29800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362452936121805990, 362452948445638580⟩, ⟨974168673725170721, 974417165757124935⟩, true⟩

def words02 : List Nat := [371285619017727270, 371285619018688528, 371285618302844046, 371285617592807252, 371285616882440586, 371285616511807457, 371285615588631005, 371285615138303400, 371285614687693360, 371285614123337445]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 29820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 29800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362522068939135271, 362522081271617515⟩, ⟨(-1088402506120682080), (-1088153756025896182)⟩, true⟩

def words03 : List Nat := [371285613028963010, 371285612732060127, 371285613257336184, 371285613258308567, 371285613145848597, 371285612882797344, 371285613475849772, 371285613769093875, 371285614991844626, 371285616214949646]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 29830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 29800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362470668374657048, 362470680715776577⟩, ⟨445518712201819891, 445767720076786951⟩, true⟩

def words04 : List Nat := [371285617144842015, 371285617145798511, 371285616986557240, 371285617197039715, 371285617645885282, 371285617646841532, 371285616602018447, 371285615563051636, 371285614523736495, 371285614307738949]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 29840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 29800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362465100682491508, 362465113032207738⟩, ⟨611943276146625971, 612192540677853659⟩, true⟩

def words05 : List Nat := [371285614427240244, 371285615047352983, 371285615679408765, 371285615680373154, 371285615579084193, 371285615517915853, 371285616379651803, 371285616380608398, 371285615812236681, 371285615126671163]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 29850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 29800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483302185836800, 362483314544127939⟩, ⟨68508181901699726, 68757702522997742⟩, true⟩

def words06 : List Nat := [371285614493137607, 371285614494220568, 371285614971299507, 371285615769721719, 371285616260824143, 371285616261781092, 371285615711363044, 371285615996069396, 371285616441446724, 371285616442438050]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 29860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 29800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498951706902647, 362498964073934223⟩, ⟨(-398963382968002147), (-398713601226160715)⟩, true⟩

def words07 : List Nat := [371285616366099582, 371285616274758351, 371285617208481784, 371285617818649068, 371285618732267719, 371285619646206082, 371285620466720439, 371285620467677939, 371285620244041066, 371285620691810929]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 29870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 29800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469981003023068, 362469993378598385⟩, ⟨466906220673612603, 467156257746219559⟩, true⟩

def words08 : List Nat := [371285622256355802, 371285622508915638, 371285622517792525, 371285622526970906, 371285622776164621, 371285622777222426, 371285622611091052, 371285622633796763, 371285622634521112, 371285622560858212]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 29880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 29800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362504538369884255, 362504550754103883⟩, ⟨(-566151033318963158), (-565900737824793480)⟩, true⟩

def words09 : List Nat := [371285622468101539, 371285622898673503, 371285624303870013, 371285624304828058, 371285624220917381, 371285623948184933, 371285623870110012, 371285623871182320, 371285624306948631, 371285624940993125]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 29890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 29800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 29800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk298
