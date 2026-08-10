import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk498A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590569259525665, 360590584812698097⟩, ⟨(-433436883967430847), (-432913513257347267)⟩, true⟩

def state01 : KState := ⟨⟨360603954806312353, 360603970365952607⟩, ⟨(-1100153046127332772), (-1099629353286484502)⟩, true⟩

def words00 : List Nat := [360581892522026472, 360581892870675340, 360581892961107853, 360581893051608938, 360581893052194082, 360581892863683352, 360581893272051067, 360581893680538573, 360581893887558411, 360581894331476558]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 49800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 49800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360617365241653547, 360617380807791288⟩, ⟨(-1768126783882728692), (-1767602767371277406)⟩, true⟩

def words01 : List Nat := [360581895177204719, 360581896023113400, 360581897190955428, 360581897956893590, 360581898352845024, 360581898748830653, 360581899387996427, 360581900311771782, 360581901024514743, 360581901737371761]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 49810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 49800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360624040552646490, 360624056125329466⟩, ⟨(-2100852845129950080), (-2100328502501977024)⟩, true⟩

def words02 : List Nat := [360581902248876421, 360581902550869107, 360581903254494592, 360581903958300295, 360581904553013729, 360581905159482908, 360581905481460267, 360581905803498201, 360581906244899512, 360581907091545236]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 49820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 49800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360570811591190782, 360570827170349121⟩, ⟨551954198153260186, 552478863481425366⟩, true⟩

def words03 : List Nat := [360581908339584502, 360581909587705356, 360581910531986812, 360581911074668543, 360581911517397461, 360581911960290625, 360581912401311715, 360581912440857053, 360581912441469939, 360581912219776919]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 49830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 49800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582090307306837, 360582105892955824⟩, ⟨(-10237611881572981), (-9712623027943127)⟩, true⟩

def words04 : List Nat := [360581911997929303, 360581911679153739, 360581911988148820, 360581912343799926, 360581912353164305, 360581912353852138, 360581911961656158, 360581911560671799, 360581911159501411, 360581911059892738]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 49840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 49800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk498A
