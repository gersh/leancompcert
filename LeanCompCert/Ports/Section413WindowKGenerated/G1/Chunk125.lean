import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk125

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362523530994564163, 362523533001356000⟩, ⟨(-488602367491026227), (-488585392697635843)⟩, true⟩

def state01 : KState := ⟨⟨362496811927529002, 362496813937684568⟩, ⟨(-154379517018158247), (-154362500160939369)⟩, true⟩

def words00 : List Nat := [371284452496767747, 371284452497146977, 371284458185593531, 371284464215649598, 371284470916435551, 371284472226199273, 371284472226479819, 371284472200285340, 371284474808546925, 371284475795237047]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 12500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 12500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492558966627599, 362492560980140917⟩, ⟨(-100903114954456243), (-100886056074641261)⟩, true⟩

def words01 : List Nat := [371284483147992381, 371284490499729680, 371284497085672710, 371284497086045062, 371284495212164794, 371284495240952759, 371284501630067680, 371284502344076557, 371284502988020394, 371284503631999823]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 12510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 12500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484373625838860, 362484375642693665⟩, ⟨1857614717045393, 1874715449104377⟩, true⟩

def words02 : List Nat := [371284508980067965, 371284511135809211, 371284515952178124, 371284520767921313, 371284524423795014, 371284524424167755, 371284521145736052, 371284522681982535, 371284525260453715, 371284525260846028]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 12520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 12500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483801339003696, 362483803359250676⟩, ⟨9150838798750878, 9167982052207900⟩, true⟩

def words03 : List Nat := [371284525258926640, 371284525269069223, 371284530664065574, 371284532870803894, 371284535863385493, 371284538855634631, 371284540912951751, 371284540913324937, 371284534516142969, 371284534458297902]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 12530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 12500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362461477418192577, 362461479441766306⟩, ⟨289332061751356935, 289349246739213357⟩, true⟩

def words04 : List Nat := [371284540679069681, 371284540679443106, 371284538507437784, 371284535867373883, 371284533227577639, 371284531843576420, 371284530534997137, 371284533047332918, 371284535158250978, 371284535158637957]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 12540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 12500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362529634475038738, 362529636501999323⟩, ⟨(-566602035827550429), (-566584808317724347)⟩, true⟩

def words05 : List Nat := [371284533321935468, 371284531875039557, 371284535310687185, 371284535311060867, 371284531755748742, 371284527545645203, 371284523752859207, 371284523753280216, 371284526246135431, 371284529837854930]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 12550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 12500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470375760238825, 362470377790570990⟩, ⟨177754355421859899, 177771625296294209⟩, true⟩

def words06 : List Nat := [371284533335154805, 371284533335531427, 371284533018853459, 371284534824847597, 371284536828742427, 371284536829116814, 371284531609076861, 371284525741100142, 371284520321989964, 371284520322416360]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 12560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 12500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362404910447970872, 362404912481678365⟩, ⟨1001202918599574356, 1001220230919161588⟩, true⟩

def words07 : List Nat := [371284522145347556, 371284525092976044, 371284526800961281, 371284526801335886, 371284520098914179, 371284515301853733, 371284512014930969, 371284512015306409, 371284507061983471, 371284500735328537]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 12570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 12500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362527436648524386, 362527438685587585⟩, ⟨(-540669191376400314), (-540651836824793280)⟩, true⟩

def words08 : List Nat := [371284494409516357, 371284492416190532, 371284488384902344, 371284489520217424, 371284489637112824, 371284489637494767, 371284487230784426, 371284488331855688, 371284495727548532, 371284499138544079]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 12580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 12500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471462593783577, 362471464634278336⟩, ⟨164407559984972575, 164424957756736371⟩, true⟩

def words09 : List Nat := [371284502456534529, 371284505774126246, 371284511507374217, 371284514095311784, 371284516727523599, 371284519359455582, 371284521504298985, 371284521504674459, 371284515269385092, 371284514234100300]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 12590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 12500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 12500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk125
