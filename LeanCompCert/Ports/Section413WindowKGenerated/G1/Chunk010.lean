import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk010

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362226788737721934, 362226788747577509⟩, ⟨197159867472022664, 197159874182935698⟩, true⟩

def state01 : KState := ⟨⟨361766724474083148, 361766724484148792⟩, ⟨658376809404468424, 658376816326525822⟩, true⟩

def words00 : List Nat := [371223751658865506, 371223577393900652, 371222928632165289, 371222777394358540, 371222626457515691, 371222276031767765, 371220636386670089, 371219629959608686, 371218625527434665, 371218582718135452]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 1000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 1000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361996698936828990, 361996698947109974⟩, ⟨426401304778945932, 426401311919607154⟩, true⟩

def words01 : List Nat := [371217937952343134, 371217276260676862, 371216910413211900, 371216910413237949, 371216835579735274, 371216719419414848, 371216603487523858, 371216507005237083, 371215149694794086, 371214739448991942]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 1010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 1000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361676656720803958, 361676656731298703⟩, ⟨758701623212605793, 758701630572411155⟩, true⟩

def words02 : List Nat := [371214863951826837, 371214863951851113, 371214677901780001, 371214356141309653, 371214035008655398, 371213867996442935, 371213371184826002, 371213408141892223, 371213408141910517, 371213260256126287]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 1020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 1000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨363618873866190498, 363618873876904016⟩, ⟨(-1249952743490038218), (-1249952735903787814)⟩, true⟩

def words03 : List Nat := [371212760572221231, 371212974927914770, 371214114936284222, 371214532868797316, 371214727606476555, 371214921968584380, 371215599752098007, 371215839482342240, 371216996246199747, 371218150787659264]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 1030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 1000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362143670508837501, 362143670519771464⟩, ⟨286957663253521094, 286957671070179816⟩, true⟩

def words04 : List Nat := [371219274199472912, 371219274199497294, 371219423144481173, 371219657734544765, 371219909008998971, 371219909009023454, 371218961823014934, 371217994995568520, 371217030011443863, 371216963539838302]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 1040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 1000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361808297385687786, 361808297396843098⟩, ⟨646169553613681487, 646169561663898689⟩, true⟩

def words05 : List Nat := [371217338959124039, 371217973202903206, 371218598491275323, 371218598491299997, 371218526956511754, 371218615489067568, 371219026559448392, 371219026559473102, 371218466954571976, 371217891322941116]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 1050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 1000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨363022279706696869, 363022279718074315⟩, ⟨(-643359437574173848), (-643359429287344644)⟩, true⟩

def words06 : List Nat := [371217620123314211, 371217620123341560, 371218257474939811, 371219012432327844, 371219621905892408, 371219621905917370, 371219709278948575, 371219925680597001, 371221009223387424, 371221570633772406]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 1060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 1000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨363065993962728172, 363065993974334908⟩, ⟨(-691482001520470894), (-691481992987142968)⟩, true⟩

def words07 : List Nat := [371221876058740744, 371222180914425579, 371222969770966198, 371223341847794800, 371223922821994411, 371224502717328238, 371225065246638271, 371225139485882974, 371225732869685826, 371226325155660401]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 1070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 1000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362183945782637714, 362183945794469915⟩, ⟨266084580319137473, 266084589097148501⟩, true⟩

def words08 : List Nat := [371227425441105125, 371227425441130374, 371227406125119971, 371227362116134956, 371227324471010898, 371227324471038707, 371227354860881286, 371227788414699288, 371228060096367607, 371228060096393905]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 1080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 1000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨363508212628365358, 363508212640428980⟩, ⟨(-1181583829476459723), (-1181583820445008239)⟩, true⟩

def words09 : List Nat := [371228446832188332, 371229056203705334, 371230496775680063, 371230837719048080, 371231079689767446, 371231321219345089, 371232390008900923, 371233068126783715, 371234045530904814, 371235021159552497]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 1090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 1000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 1000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk010
