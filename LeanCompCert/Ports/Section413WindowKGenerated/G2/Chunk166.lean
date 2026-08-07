import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk166

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360384937863405615, 360384939435977958⟩, ⟨3286374763483370162, 3286392435916889678⟩, true⟩

def state01 : KState := ⟨⟨360555537396646926, 360555538971195882⟩, ⟨453441119140482467, 453458824395495727⟩, true⟩

def words00 : List Nat := [360582902958581648, 360582892036452399, 360582882922702936, 360582877425918735, 360582871929778616, 360582863105266786, 360582854160099081, 360582848830588683, 360582843501659566, 360582839321851843]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 16600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 16600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360592047907823523, 360592049484368578⟩, ⟨(-153426646335986986), (-153408907915894480)⟩, true⟩

def words01 : List Nat := [360582837678531302, 360582833301961147, 360582828925878035, 360582826580060299, 360582826580235732, 360582825684146312, 360582824788141863, 360582821602821485, 360582819104592372, 360582819660175335]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 16610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 16600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360502230950063000, 360502232528581065⟩, ⟨1339576026414783935, 1339593797636295271⟩, true⟩

def words02 : List Nat := [360582820725404113, 360582820725613759, 360582818202735610, 360582813844413378, 360582809486584877, 360582802372447543, 360582797955820869, 360582794543980921, 360582791132528695, 360582785372696297]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 16620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 16600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590999570782268, 360591001151282893⟩, ⟨(-136983938879632382), (-136966134678227746)⟩, true⟩

def words03 : List Nat := [360582780529330229, 360582779290207600, 360582780415262360, 360582780415472133, 360582779195899082, 360582774941666385, 360582770687905137, 360582769518301307, 360582770013163484, 360582770508011562]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 16630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 16600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594486278201571, 360594487860702010⟩, ⟨(-195798503977913520), (-195780666490056938)⟩, true⟩

def words04 : List Nat := [360582770508200243, 360582768893999244, 360582765167178281, 360582760001777104, 360582754836940872, 360582748724319787, 360582744487167661, 360582738212578948, 360582731938703940, 360582729968293743]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 16640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 16600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360550057993352900, 360550059577834656⟩, ⟨544466974510050130, 544484844996663108⟩, true⟩

def words05 : List Nat := [360582734270587818, 360582738572405573, 360582739848065184, 360582740653362602, 360582740653538540, 360582740512851843, 360582743824488702, 360582743824698893, 360582743703010439, 360582741741399882]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 16650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 16600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360641005628755536, 360641007215220314⟩, ⟨(-971015912896806795), (-970998009362928013)⟩, true⟩

def words06 : List Nat := [360582741410571234, 360582744836538643, 360582749755050167, 360582754673011188, 360582755883702877, 360582756127214493, 360582756261946959, 360582756396723675, 360582758984087107, 360582762478290141]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 16660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 16600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360620204452066935, 360620206040534761⟩, ⟨(-623999023341571080), (-623981086406954520)⟩, true⟩

def words07 : List Nat := [360582764162713653, 360582765846958137, 360582771116403329, 360582779205342955, 360582784838080212, 360582790470177038, 360582793622257955, 360582794859213574, 360582797102261237, 360582799345108411]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 16670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 16600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360524566273113281, 360524567863565389⟩, ⟨971627726776479562, 971645696818787248⟩, true⟩

def words08 : List Nat := [360582801482731838, 360582802175266733, 360582802175454288, 360582800653834281, 360582799132362403, 360582795907542003, 360582794656600405, 360582792072769204, 360582789489221103, 360582785101241770]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 16680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 16600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360716766373484057, 360716767965924424⟩, ⟨(-2237278234224434821), (-2237260230988526177)⟩, true⟩

def words09 : List Nat := [360582781704027846, 360582781794807299, 360582785463167545, 360582788008501210, 360582788008700443, 360582787181725061, 360582787816365100, 360582792264536255, 360582800287203886, 360582808308958463]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 16690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 16600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 16600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk166
