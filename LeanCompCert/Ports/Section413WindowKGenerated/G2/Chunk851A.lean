import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk851A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590885647470969, 360590933044702152⟩, ⟨(-727923434451779989), (-725199502483796035)⟩, true⟩

def state01 : KState := ⟨⟨360601645402282936, 360601692811152163⟩, ⟨(-1643728996762865467), (-1641004074337782335)⟩, true⟩

def words00 : List Nat := [360582411429057686, 360582411430283776, 360582411510175055, 360582411619968744, 360582411694646966, 360582411773332071, 360582411774428834, 360582411747896300, 360582411831325257, 360582412059259485]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 85100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 85100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580564737143527, 360580612157547567⟩, ⟨150545612274470433, 153271516484840211⟩, true⟩

def words01 : List Nat := [360582412327681742, 360582412596327405, 360582412758389768, 360582412782550647, 360582412783574911, 360582412742611557, 360582412753594312, 360582412828533036, 360582412829625529, 360582412809761910]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 85110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 85100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587814151820241, 360587861583761269⟩, ⟨(-466488783018291282), (-463761896721403482)⟩, true⟩

def words02 : List Nat := [360582412906355326, 360582413093853466, 360582413345932902, 360582413598245296, 360582413727191502, 360582413774764267, 360582413818513127, 360582413862602968, 360582413891942701, 360582413957200776]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 85120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 85100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583623781113304, 360583671224717478⟩, ⟨(-109699688325244566), (-106971809089459756)⟩, true⟩

def words03 : List Nat := [360582413958301788, 360582413954630632, 360582414083704735, 360582414324691330, 360582414530570602, 360582414736648038, 360582414829765835, 360582414830989151, 360582414800828898, 360582414817004515]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 85130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 85100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582409617389299, 360582457072519397⟩, ⟨(-6413924262197295), (-3685063650673479)⟩, true⟩

def words04 : List Nat := [360582414829187983, 360582414830411346, 360582414704756409, 360582414500190518, 360582414295428743, 360582414056273475, 360582413904671809, 360582413891150113, 360582413877484138, 360582413795709370]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 85140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 85100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk851A
