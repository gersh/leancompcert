import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk807A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk807B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk807A

def state06 : KState := ⟨⟨360571033312180129, 360571075825195488⟩, ⟨890454527433629912, 892773312402476300⟩, true⟩

def words05 : List Nat := [360582130347494740, 360582130335452714, 360582130381391163, 360582130532808535, 360582130619407592, 360582130706197799, 360582130714022165, 360582130715177877, 360582130608017622, 360582130472451587]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580811309390087, 360580853833292206⟩, ⟨100750954154532245, 103070618392069459⟩, true⟩

def words06 : List Nat := [360582130352748049, 360582130353911596, 360582130348065511, 360582130265721252, 360582130183191199, 360582130028005982, 360582130005031354, 360582130020148579, 360582130021185671, 360582129933557058]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360586413684659605, 360586456219480237⟩, ⟨(-351883101792138961), (-349562555612077055)⟩, true⟩

def words07 : List Nat := [360582129954089098, 360582129990758291, 360582129991715569, 360582129949481497, 360582129754223124, 360582129426112909, 360582129097787740, 360582128922871183, 360582128877886253, 360582128932672547]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591036793825623, 360591079339656821⟩, ⟨(-725445889434182105), (-723124453765628047)⟩, true⟩

def words08 : List Nat := [360582128933702587, 360582128911854996, 360582128950713487, 360582129047494604, 360582129085481011, 360582129086638016, 360582129032972858, 360582128861598810, 360582128690005089, 360582128782617478]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579348788140445, 360579391344855660⟩, ⟨218957729156905338, 221280044199920286⟩, true⟩

def words09 : List Nat := [360582129022700622, 360582129262999305, 360582129413124726, 360582129611622573, 360582129683553269, 360582129755777549, 360582129925998734, 360582129990927845, 360582129991959678, 360582129959264075]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk807B
