import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk277

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362433535508758254, 362433546069660322⟩, ⟨1430962267063233146, 1431160023148757050⟩, true⟩

def state01 : KState := ⟨⟨362474597867586128, 362474608436383886⟩, ⟨293463228792795729, 293661203629710171⟩, true⟩

def words00 : List Nat := [371285210631941667, 371285210068249571, 371285209000103933, 371285208788230465, 371285208576091137, 371285208156562385, 371285206655271100, 371285206270133977, 371285206097093221, 371285206098008921]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 27700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 27700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362453943812526260, 362453954389400585⟩, ⟨865913426009679100, 866111624686069874⟩, true⟩

def words01 : List Nat := [371285205716240518, 371285205333923339, 371285204951274585, 371285204877256277, 371285204238200980, 371285203742887090, 371285203247315517, 371285202751674141, 371285200523575007, 371285199397506144]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 27710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 27700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362418024603027126, 362418035187758646⟩, ⟨1861850907703052421, 1862049324222342591⟩, true⟩

def words02 : List Nat := [371285198270983288, 371285198089818195, 371285196388529010, 371285194687742869, 371285192986750581, 371285191696384964, 371285189756369336, 371285187991932037, 371285186227323900, 371285184460179214]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 27720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 27700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362496019890469992, 362496030483171249⟩, ⟨(-301406299585472396), (-301207662024275632)⟩, true⟩

def words03 : List Nat := [371285182039331985, 371285180281592259, 371285178523533311, 371285178062989213, 371285176560264569, 371285174858712112, 371285173156916886, 371285172752436776, 371285172239142415, 371285172631542820]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 27730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 27700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491442101442571, 362491452702132427⟩, ⟨(-174465689196012088), (-174266829990959594)⟩, true⟩

def words04 : List Nat := [371285172765006094, 371285172765899865, 371285172811587797, 371285173483399769, 371285174473061461, 371285174473945244, 371285173734697232, 371285172996645219, 371285172815357998, 371285173042661023]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 27740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 27700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362449103175683724, 362449113784336145⟩, ⟨1000820616272883313, 1001019696480247969⟩, true⟩

def words05 : List Nat := [371285174565436311, 371285176088467656, 371285177283927838, 371285177284811723, 371285176752142093, 371285176214809588, 371285176136328517, 371285176137212558, 371285174869699867, 371285173571673330]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 27750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 27700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362458197116448105, 362458207733026082⟩, ⟨748437681301899097, 748636981563667389⟩, true⟩

def words06 : List Nat := [371285172273339793, 371285171405444470, 371285170064985382, 371285170019680953, 371285169974113726, 371285169717934281, 371285167734910763, 371285167046858768, 371285166358397838, 371285166212736693]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 27760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 27700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485546510080310, 362485557134710043⟩, ⟨(-11206164844423749), (-11006640944692729)⟩, true⟩

def words07 : List Nat := [371285165242656678, 371285164272332559, 371285163624385983, 371285163625369271, 371285163303296792, 371285162936174051, 371285162568750918, 371285162190555502, 371285160926248171, 371285160941594436]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 27770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 27700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471068340729381, 362471078973250579⟩, ⟨391081699676738923, 391281442842605689⟩, true⟩

def words08 : List Nat := [371285161809848376, 371285161810734071, 371285161293123065, 371285160522141920, 371285159750869620, 371285159371733920, 371285158708250489, 371285158876063847, 371285158909088952, 371285158910020734]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 27780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 27700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362522447794766571, 362522458435298991⟩, ⟨(-1036930403827320620), (-1036730437989508714)⟩, true⟩

def words09 : List Nat := [371285159189490037, 371285159976017693, 371285162054022105, 371285162899944159, 371285163447512958, 371285163995307104, 371285164579414043, 371285164630392106, 371285165972497671, 371285167314908016]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 27790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 27700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 27700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk277
