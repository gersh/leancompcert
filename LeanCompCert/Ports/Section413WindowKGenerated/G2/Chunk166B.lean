import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk166A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk166B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk166A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk166B
