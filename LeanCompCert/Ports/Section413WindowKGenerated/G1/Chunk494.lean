import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk494

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483194225788827, 362483229453599801⟩, ⟨85187097462083422, 86362820287628256⟩, true⟩

def state01 : KState := ⟨⟨362476862058246656, 362476897300927189⟩, ⟨397948589114446504, 399125046570504822⟩, true⟩

def words00 : List Nat := [371284977654691192, 371284977545402446, 371284977015311515, 371284976850622774, 371284976685143513, 371284976575091512, 371284976123145682, 371284975652798066, 371284975181776933, 371284975120125135]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 49400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 49400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362468176224442541, 362468211481960956⟩, ⟨827262871185212141, 828440061856619909⟩, true⟩

def words01 : List Nat := [371284975202838939, 371284975449691191, 371284975640040107, 371284975641689008, 371284975371709359, 371284975229889842, 371284975351870015, 371284975353517732, 371284975074296007, 371284974736956032]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 49410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 49400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476828420559421, 362476863692815220⟩, ⟨399685464929397330, 400863383999980386⟩, true⟩

def words02 : List Nat := [371284974432874257, 371284974434689706, 371284974304589801, 371284974346219238, 371284974347496283, 371284974334162187, 371284973928767315, 371284973620545102, 371284973409579824, 371284973411285785]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 49420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 49400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490700157149941, 362490735444443968⟩, ⟨(-286020435291544469), (-284841772806591347)⟩, true⟩

def words03 : List Nat := [371284973248456829, 371284973087385677, 371284973170987720, 371284973311966520, 371284973579505841, 371284973847654514, 371284974115444273, 371284974117096368, 371284974079659795, 371284974198255449]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 49430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 49400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474824682594339, 362474859984584616⟩, ⟨498921738261657820, 500101127403961134⟩, true⟩

def words04 : List Nat := [371284974478612876, 371284974480261858, 371284974272849685, 371284974067183782, 371284973860920035, 371284973649084385, 371284973266772097, 371284973265357538, 371284973263341910, 371284973253086213]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 49440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 49400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362501846222962842, 362501881539835086⟩, ⟨(-837424677442314357), (-836244552310586785)⟩, true⟩

def words05 : List Nat := [371284973253094507, 371284973458449930, 371284973924829217, 371284973926478482, 371284973903324593, 371284973766194755, 371284973767199171, 371284973769016071, 371284974046039177, 371284974389710532]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 49450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 49400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478618120287984, 362478653452054412⟩, ⟨311579594140717610, 312760456014602734⟩, true⟩

def words06 : List Nat := [371284974733877363, 371284974737871529, 371284975149045634, 371284975561091266, 371284976045964862, 371284976047614263, 371284975988493247, 371284975849825415, 371284975710528014, 371284975676756547]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 49460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 49400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486214960357436, 362486250307002256⟩, ⟨(-64237759102687160), (-63056161120739628)⟩, true⟩

def words07 : List Nat := [371284975765786438, 371284975983297537, 371284976163034417, 371284976164685769, 371284975901042390, 371284975757485394, 371284975875070695, 371284975901403775, 371284975928393603, 371284975956016611]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 49470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 49400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485440539686171, 362485475901115406⟩, ⟨(-25834929524578209), (-24652599933697593)⟩, true⟩

def words08 : List Nat := [371284976390371609, 371284976622643184, 371284977025784498, 371284977429545900, 371284977761956047, 371284977763606621, 371284977606742697, 371284977594471353, 371284977766421856, 371284977778225715]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 49480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 49400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486951524615209, 362486986901069948⟩, ⟨(-100591232716768139), (-99408159439786987)⟩, true⟩

def words09 : List Nat := [371284977779478901, 371284977777458077, 371284978109092187, 371284978278136374, 371284978538094496, 371284978798687999, 371284978976677216, 371284978978328058, 371284978653364587, 371284978695994500]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 49490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 49400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 49400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk494
