import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk301

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470277976000778, 362470290533513640⟩, ⟨459616212430076168, 459871706760113410⟩, true⟩

def state01 : KState := ⟨⟨362474892531352625, 362474905097498440⟩, ⟨320858575749196102, 321114329975611748⟩, true⟩

def words00 : List Nat := [371285568559255117, 371285568560319606, 371285569637749275, 371285570727813340, 371285571577751193, 371285571578716859, 371285570960308103, 371285570208254423, 371285569803572186, 371285569804571692]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 30100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 30100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362510406648331600, 362510419223284450⟩, ⟨(-748649141761536500), (-748393122309980304)⟩, true⟩

def words01 : List Nat := [371285569451114549, 371285569100242002, 371285569497785793, 371285569840829768, 371285570433594133, 371285571026677888, 371285571621653510, 371285571622626558, 371285572172867238, 371285572998978817]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 30110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 30100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362471464745213531, 362471477328783330⟩, ⟨424437422898553755, 424693701937767925⟩, true⟩

def words02 : List Nat := [371285574066878056, 371285574067844196, 371285573668965572, 371285573260062587, 371285572850824596, 371285572753000361, 371285572368733141, 371285572635438134, 371285572704547169, 371285572705548607]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 30120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 30100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362546061326471380, 362546073918764956⟩, ⟨(-1823536438014186740), (-1823279896083883832)⟩, true⟩

def words03 : List Nat := [371285572592687349, 371285572948106426, 371285574402240403, 371285575124455833, 371285575485902406, 371285575847620127, 371285577307892232, 371285578217231438, 371285580225044554, 371285582233151212]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 30130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 30100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362509866718786016, 362509879319817246⟩, ⟨(-732443101745208020), (-732186296417550838)⟩, true⟩

def words04 : List Nat := [371285584147524654, 371285585146503224, 371285587050738825, 371285588955361294, 371285591192938581, 371285591966260039, 371285592724492399, 371285593482987842, 371285594532752611, 371285595339305239]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 30140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 30100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362478476545920683, 362478489155671691⟩, ⟨214190381599069170, 214447449871748958⟩, true⟩

def words05 : List Nat := [371285596714542090, 371285598090083959, 371285599359558975, 371285599360526084, 371285599166222349, 371285599130737836, 371285599966018665, 371285599966988557, 371285599716915655, 371285599482258951]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 30150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 30100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362508054224797926, 362508066843213679⟩, ⟨(-677972874013127009), (-677715544366713107)⟩, true⟩

def words06 : List Nat := [371285600108745217, 371285600594466588, 371285601448606424, 371285602303061488, 371285602976823503, 371285602977791139, 371285602298249284, 371285602408846335, 371285603615666492, 371285604361215512]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 30160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 30100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489926235071661, 362489938862290657⟩, ⟨(-130946402262753601), (-130688806978309951)⟩, true⟩

def words07 : List Nat := [371285605100355278, 371285605839765270, 371285606877292249, 371285607471073474, 371285608124906414, 371285608779078388, 371285609238795218, 371285609239763468, 371285608549408073, 371285608694072961]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 30170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 30100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486369334364544, 362486381970207736⟩, ⟨(-23517449011076902), (-23259593404010396)⟩, true⟩

def words08 : List Nat := [371285609934169459, 371285609935137771, 371285609714095394, 371285609495375615, 371285609389410942, 371285609390493856, 371285609967590072, 371285610804526187, 371285611528880832, 371285611555401867]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 30180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 30100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362507963314038183, 362507975958659712⟩, ⟨(-675573511096476970), (-675315390428252588)⟩, true⟩

def words09 : List Nat := [371285611819582785, 371285612084250108, 371285613341534004, 371285613376758883, 371285613377520822, 371285613027811631, 371285613421956240, 371285613779661773, 371285614520793223, 371285615262310974]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 30190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 30100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 30100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk301
