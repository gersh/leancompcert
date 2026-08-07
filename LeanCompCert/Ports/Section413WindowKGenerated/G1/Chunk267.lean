import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk267

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362466232549649912, 362466242331523694⟩, ⟨505546776813237375, 505723340616819747⟩, true⟩

def state01 : KState := ⟨⟨362447328554629556, 362447338344050773⟩, ⟨1010522847377443590, 1010699612736824192⟩, true⟩

def words00 : List Nat := [371285183263347297, 371285183264198958, 371285182715025025, 371285182039390954, 371285181363483764, 371285180759988019, 371285179458165485, 371285179038084735, 371285178617752776, 371285178089941332]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 26700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 26700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362507566689373493, 362507576486481605⟩, ⟨(-598588203991694218), (-598411233277555494)⟩, true⟩

def words01 : List Nat := [371285176673882060, 371285176658397121, 371285178025802216, 371285178120263094, 371285178120922925, 371285178044793574, 371285179290821134, 371285180016748325, 371285180855529671, 371285181694622111]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 26710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 26700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362519684114412792, 362519693919182978⟩, ⟨(-922567536985682639), (-922390361502572017)⟩, true⟩

def words02 : List Nat := [371285182540888017, 371285182541736857, 371285182514047767, 371285183200444792, 371285184315774380, 371285184554948738, 371285184648826972, 371285184742995019, 371285186235389895, 371285187527297057]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 26720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 26700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362506187651822394, 362506197464229224⟩, ⟨(-561615902540990627), (-561438522890896233)⟩, true⟩

def words03 : List Nat := [371285190217185486, 371285192907209224, 371285195223119016, 371285195675371287, 371285196549178704, 371285197423349814, 371285199694747108, 371285200472354844, 371285201258223818, 371285202044353719]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 26730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 26700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494303632106060, 362494313452104289⟩, ⟨(-243735017149059513), (-243557434465214629)⟩, true⟩

def words04 : List Nat := [371285203027141916, 371285203314771386, 371285204736538525, 371285206158550619, 371285207365660254, 371285207366509657, 371285207146046167, 371285207326457684, 371285208500403405, 371285208841642430]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 26740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 26700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362521615639229125, 362521625466977398⟩, ⟨(-974465519094436618), (-974287729058641204)⟩, true⟩

def words05 : List Nat := [371285209042729256, 371285209244106351, 371285210603336031, 371285211586103267, 371285212989801667, 371285214393711455, 371285215778170997, 371285215779022581, 371285217105341635, 371285218466900472]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 26750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 26700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362459479041447940, 362459488876772160⟩, ⟨688624679411280902, 688802672219493686⟩, true⟩

def words06 : List Nat := [371285220407887441, 371285220489410309, 371285220490050345, 371285220291246194, 371285220141940104, 371285220142884412, 371285219493068730, 371285219420805128, 371285219348234519, 371285219271700046]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 26760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 26700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362518318532298388, 362518328375291390⟩, ⟨(-886817415484466369), (-886639217344063375)⟩, true⟩

def words07 : List Nat := [371285218349612373, 371285218389080605, 371285219489342761, 371285219490198266, 371285219343346173, 371285218703540367, 371285218816410852, 371285218876868577, 371285220113797830, 371285221351007605]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 26770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 26700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487780437599422, 362487790288274001⟩, ⟨(-68838795754214797), (-68660391863429637)⟩, true⟩

def words08 : List Nat := [371285222624034213, 371285222740715596, 371285224250287470, 371285225760208676, 371285227327588604, 371285227328439051, 371285227255763483, 371285227178787487, 371285227376071948, 371285227472706705]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 26780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 26700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362454890169062254, 362454900027409306⟩, ⟨812616966273198259, 812795575747056285⟩, true⟩

def words09 : List Nat := [371285228785053247, 371285230097656421, 371285231329862573, 371285231330713310, 371285230707545821, 371285230229197476, 371285230477461156, 371285230478312179, 371285229351257697, 371285228220534197]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 26790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 26700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 26700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk267
