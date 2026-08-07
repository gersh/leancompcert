import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk937

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360568989306849383, 360569047198670811⟩, ⟨1216901499962960682, 1220564430742219886⟩, true⟩

def state01 : KState := ⟨⟨360585617470607551, 360585675375256395⟩, ⟨(-341146901679820109), (-337482768909786415)⟩, true⟩

def words00 : List Nat := [360582073362035938, 360582073414075143, 360582073604700361, 360582073795592186, 360582073889618972, 360582073890975559, 360582073939996126, 360582074010250495, 360582074021073027, 360582074060907922]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360585875086589647, 360585933004151361⟩, ⟨(-365300809835680651), (-361635466936710147)⟩, true⟩

def words01 : List Nat := [360582074062116432, 360582074044751052, 360582074077849373, 360582074186875048, 360582074266860471, 360582074347089336, 360582074351823994, 360582074353181179, 360582074322834677, 360582074365565167]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575123492560387, 360575181422916371⟩, ⟨642299372358771712, 645965914399071078⟩, true⟩

def words02 : List Nat := [360582074398330879, 360582074399687692, 360582074319035300, 360582074150944741, 360582073982639334, 360582073748828701, 360582073588550979, 360582073478344061, 360582073367990117, 360582073196248272]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582322080479306, 360582380023627582⟩, ⟨(-32515249245244641), (-28847508118501529)⟩, true⟩

def words03 : List Nat := [360582073123825356, 360582073068953412, 360582073037416651, 360582073038773670, 360582072950249616, 360582072764330643, 360582072578174923, 360582072388722780, 360582072282643261, 360582072287331634]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583727185377500, 360583785141452245⟩, ⟨(-164323804095759388), (-160654851178183160)⟩, true⟩

def words04 : List Nat := [360582072288540461, 360582072236075897, 360582072165411735, 360582072129067101, 360582072092320336, 360582072027161373, 360582071911674287, 360582071739244051, 360582071566555308, 360582071507985102]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360554817570610087, 360554875539480481⟩, ⟨2546066426547538696, 2549736579121768282⟩, true⟩

def words05 : List Nat := [360582071509101438, 360582071497515042, 360582071485800317, 360582071386663177, 360582071173839482, 360582070895062142, 360582070615886357, 360582070349341532, 360582070117572933, 360582069828933572]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576116215902807, 360576174197580297⟩, ⟨549047473275025607, 552718826706858885⟩, true⟩

def words06 : List Nat := [360582069539992255, 360582069365152986, 360582069247418981, 360582069243637631, 360582069239766599, 360582069137856549, 360582068945916780, 360582068822002752, 360582068697697807, 360582068607591035]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360558633167317003, 360558691161947866⟩, ⟨2188555991396647664, 2192228559529384344⟩, true⟩

def words07 : List Nat := [360582068545955107, 360582068409392359, 360582068272544890, 360582068226403663, 360582068227549741, 360582068152767813, 360582068077839244, 360582067946014590, 360582067700542980, 360582067452836429]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360572861714044041, 360572919721463442⟩, ⟨854123060383097474, 857796827886883166⟩, true⟩

def words08 : List Nat := [360582067204669166, 360582067051229915, 360582066864188988, 360582066609948168, 360582066355488250, 360582066072819337, 360582065902367807, 360582065845792766, 360582065789085391, 360582065652030527]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580358047690190, 360580416067944067⟩, ⟨150978013952822071, 154652985264198779⟩, true⟩

def words09 : List Nat := [360582065555614219, 360582065542398276, 360582065528802904, 360582065512783987, 360582065444084083, 360582065268965992, 360582065093598686, 360582064935816847, 360582064836597520, 360582064820452215]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk937
