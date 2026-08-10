import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk979A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583135703011425, 360583199115965512⟩, ⟨(-80590176604656473), (-76398230724895575)⟩, true⟩

def state01 : KState := ⟨⟨360582663678440262, 360582727104832205⟩, ⟨(-34330368360798828), (-30137106851800414)⟩, true⟩

def words00 : List Nat := [360582418834109562, 360582419004013505, 360582419154831362, 360582419305911434, 360582419364622975, 360582419366044971, 360582419320607025, 360582419321501880, 360582419321998592, 360582419303800127]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 97900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 97900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580537369783881, 360580600809729081⟩, ⟨173847004865538494, 178041593440976480⟩, true⟩

def words01 : List Nat := [360582419305089902, 360582419216935335, 360582419128509953, 360582419173377803, 360582419195840163, 360582419218565996, 360582419219832938, 360582419183536922, 360582419061882852, 360582419044956216]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 97910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 97900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593901906229139, 360593965359586851⟩, ⟨(-1134898719296345512), (-1130702817300543156)⟩, true⟩

def words02 : List Nat := [360582419095564814, 360582419149018856, 360582419150307953, 360582419123389007, 360582419096239879, 360582419052132183, 360582419166598120, 360582419281334469, 360582419327073728, 360582419446471489]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 97920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 97900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595292216455507, 360595355683226256⟩, ⟨(-1271058337477045893), (-1266861121874352041)⟩, true⟩

def words03 : List Nat := [360582419669728616, 360582419893399119, 360582420095752990, 360582420249917531, 360582420315433836, 360582420381059549, 360582420401382171, 360582420474792343, 360582420608015456, 360582420741558575]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 97930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 97900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591986934402232, 360592050414718565⟩, ⟨(-947379968251738650), (-943181425927521990)⟩, true⟩

def words04 : List Nat := [360582420822648260, 360582420872865749, 360582421026990863, 360582421181569346, 360582421287050866, 360582421288868781, 360582421290147952, 360582421239767111, 360582421199965294, 360582421299896588]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 97940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 97900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk979A
