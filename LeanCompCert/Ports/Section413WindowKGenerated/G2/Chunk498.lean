import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk498

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

def state06 : KState := ⟨⟨360582964000036177, 360582979592240737⟩, ⟨(-53790396580512135), (-53265080899550877)⟩, true⟩

def words05 : List Nat := [360581911060511729, 360581910810718961, 360581910711680435, 360581911173224720, 360581911367307014, 360581911561492604, 360581911562105391, 360581911555271831, 360581911298611219, 360581911320828220]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 49850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 49800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360557409786422275, 360557425385113587⟩, ⟨1220336433410344729, 1220862072553842301⟩, true⟩

def words06 : List Nat := [360581911321395646, 360581911160492977, 360581910702637588, 360581909938360835, 360581909174001596, 360581908310143737, 360581907648613991, 360581907259374020, 360581906870065572, 360581906276883266]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 49860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 49800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360617660517966016, 360617676123150821⟩, ⟨(-1784698020401119592), (-1784172057396163794)⟩, true⟩

def words07 : List Nat := [360581905786555353, 360581905697488174, 360581905792536958, 360581905919633130, 360581905920280658, 360581905694333448, 360581905642588897, 360581906117321811, 360581906834999871, 360581907552805476]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 49870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 49800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360590989859911170, 360591005471654227⟩, ⟨(-454287703148392719), (-453761412984639333)⟩, true⟩

def words08 : List Nat := [360581908013541126, 360581908493323714, 360581909274416644, 360581910055679873, 360581910570116957, 360581910683884488, 360581910684504201, 360581910537276692, 360581910389932995, 360581910416173587]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 49880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 49800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360581459627059223, 360581475245288048⟩, ⟨21344402336480889, 21871016107131769⟩, true⟩

def words09 : List Nat := [360581910999737349, 360581911583409507, 360581911966281541, 360581912441008589, 360581912668120436, 360581912895430031, 360581913357145636, 360581913549660996, 360581913550274275, 360581913542204023]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 49890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 49800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 49800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk498
