import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk455A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk455B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk455A

def state06 : KState := ⟨⟨360595340968122443, 360595353890771085⟩, ⟨(-551942333222900574), (-551544474545925958)⟩, true⟩

def words05 : List Nat := [360583250146450783, 360583249837744067, 360583249700646130, 360583249701270259, 360583249393047755, 360583248676086339, 360583247959026224, 360583247731130248, 360583247997354462, 360583248263709653]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 45550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 45500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577534948487198, 360577547877088504⟩, ⟨259212045030856739, 259610174939793373⟩, true⟩

def words06 : List Nat := [360583248288175434, 360583248446759563, 360583248449459227, 360583248452332219, 360583248452857219, 360583248191756450, 360583247450206921, 360583246416701634, 360583245383122210, 360583244830675070]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 45560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 45500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360523696959053208, 360523709893531869⟩, ⟨2712975580523853650, 2713373978293688304⟩, true⟩

def words07 : List Nat := [360583244966929593, 360583245228304833, 360583245228864816, 360583245121858144, 360583244534483971, 360583243822907819, 360583243111183146, 360583242187887516, 360583241123897083, 360583239818461525]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 45570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 45500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588542075057311, 360588555015427305⟩, ⟨(-243055337565330451), (-242656671239530393)⟩, true⟩

def words08 : List Nat := [360583238512942634, 360583237419211178, 360583236615023284, 360583236160191058, 360583235705320094, 360583234838300261, 360583233755622057, 360583233153637759, 360583232551496328, 360583232546711122]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 45580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 45500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360600429902552231, 360600442848880905⟩, ⟨(-785172041313383130), (-784773103301855696)⟩, true⟩

def words09 : List Nat := [360583232547279888, 360583232265639813, 360583232069240657, 360583232508568745, 360583232631398180, 360583232754320616, 360583232754877241, 360583232636570084, 360583232911690400, 360583233289807599]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 45590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 45500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 45500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk455B
