import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk208A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk208B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk208A

def state06 : KState := ⟨⟨360499655363272054, 360499657898381300⟩, ⟨1699165644548587603, 1699201429213584583⟩, true⟩

def words05 : List Nat := [360581122838666221, 360581125877093576, 360581127103860576, 360581127104128698, 360581126039794134, 360581123760908572, 360581121489274897, 360581121489543078, 360581119206369596, 360581115301507551]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 20850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 20800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360507191178421738, 360507193716062059⟩, ⟨1542098347859073781, 1542134185334670275⟩, true⟩

def words06 : List Nat := [360581111396955068, 360581108521207028, 360581107216509880, 360581107245043299, 360581107245291668, 360581105346226925, 360581101158088091, 360581095703430449, 360581090249217245, 360581086106351215]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 20860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 20800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597688598518801, 360597691138717561⟩, ⟨(-347198445814943117), (-347162554932283083)⟩, true⟩

def words07 : List Nat := [360581082566159050, 360581077860413628, 360581073155067901, 360581070732399468, 360581070182930726, 360581068925531126, 360581067668221950, 360581065267417680, 360581064579264611, 360581065375826307]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 20870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 20800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360564455434309200, 360564457977038031⟩, ⟨346622637102709876, 346658580826221520⟩, true⟩

def words08 : List Nat := [360581065376047728, 360581065255966124, 360581063694865352, 360581060991310893, 360581058287971254, 360581055011667274, 360581053473886084, 360581053844812474, 360581053845055452, 360581052451945941]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 20880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 20800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360648072012996787, 360648074558261771⟩, ⟨(-1400853952396610613), (-1400817955680410295)⟩, true⟩

def words09 : List Nat := [360581051657828250, 360581051531440446, 360581052022072110, 360581052022340988, 360581051410770565, 360581048727173138, 360581046043781298, 360581046568114216, 360581049775412586, 360581052982467292]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 20890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 20800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 20800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk208B
