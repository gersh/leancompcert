import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk773A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360614081554730771, 360614120369729943⟩, ⟨(-2471897070557929196), (-2469870589156265868)⟩, true⟩

def state01 : KState := ⟨⟨360594176073799115, 360594214899321404⟩, ⟨(-933237368281453639), (-931210073391030193)⟩, true⟩

def words00 : List Nat := [360582169312496184, 360582169429190529, 360582169623565269, 360582169818257441, 360582169970828966, 360582169971932032, 360582169957688622, 360582169849842375, 360582169754170992, 360582169911242205]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 77300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 77300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360570295552307131, 360570334388214457⟩, ⟨913107064726284819, 915135162535745903⟩, true⟩

def words01 : List Nat := [360582170044368109, 360582170177695680, 360582170227330956, 360582170280399666, 360582170281339412, 360582170212631259, 360582170240648869, 360582170241752269, 360582170225126930, 360582170073192933]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 77310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 77300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360611052778904487, 360611091625246739⟩, ⟨(-2238420088625434017), (-2236391183938305825)⟩, true⟩

def words02 : List Nat := [360582169921012867, 360582170021158738, 360582170303839147, 360582170586728783, 360582170727597372, 360582170841958207, 360582171071178727, 360582171300729413, 360582171526021453, 360582171901152414]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 77320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 77300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603283139402680, 360603321996239573⟩, ⟨(-1637567299107449202), (-1635537582815497234)⟩, true⟩

def words03 : List Nat := [360582172179828447, 360582172458617530, 360582172794100266, 360582173213655611, 360582173591156180, 360582173968846146, 360582174243147204, 360582174350819306, 360582174625148776, 360582174899837723]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 77330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 77300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593959981667623, 360593998848919280⟩, ⟨(-916590842768428954), (-914560320949187964)⟩, true⟩

def words04 : List Nat := [360582175152604372, 360582175238850052, 360582175239851396, 360582175181623524, 360582175123217985, 360582174995260055, 360582175071157164, 360582175193183841, 360582175194171040, 360582175338932995]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 77340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 77300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk773A
