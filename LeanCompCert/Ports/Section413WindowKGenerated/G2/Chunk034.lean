import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk034

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨359929514696142912, 359929514752155511⟩, ⟨2164848130347267887, 2164848259723441967⟩, true⟩

def state01 : KState := ⟨⟨360561693718105924, 360561693774468326⟩, ⟨12129009784379878, 12129140351573650⟩, true⟩

def words00 : List Nat := [360566047613027498, 360565891598327977, 360565802078488207, 360565751318601325, 360565700588526405, 360565572872019176, 360565429747463684, 360565371250693607, 360565312788232501, 360565250707122747]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 3400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 3400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360328617143822863, 360328617200538556⟩, ⟨809242038004674346, 809242169778376176⟩, true⟩

def words01 : List Nat := [360565249664373104, 360565203528138716, 360565195589938155, 360565278914444113, 360565340205335556, 360565401460359524, 360565401460392696, 360565396277742756, 360565306925496945, 360565237718017614]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 3410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 3400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360234589764705855, 360234589821772719⟩, ⟨1129955087282969080, 1129955220259453344⟩, true⟩

def words02 : List Nat := [360565168550986478, 360565108230832814, 360565023125696833, 360564868541037411, 360564714046640447, 360564531287702809, 360564393201557599, 360564284983128755, 360564176827815703, 360564022830594718]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 3420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 3400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360610584897355703, 360610584954775207⟩, ⟨(-161343173008677722), (-161343038820874286)⟩, true⟩

def words03 : List Nat := [360563926814009216, 360563873992070361, 360563851604237904, 360563867345468573, 360563867345502974, 360563808366639237, 360563749422088962, 360563687060186520, 360563682908567662, 360563696538959783]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 3430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 3400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360094201669982853, 360094201727759547⟩, ⟨1614108939680082884, 1614109075098386440⟩, true⟩

def words04 : List Nat := [360563696538993215, 360563652551339061, 360563525746825312, 360563408281420758, 360563290884200759, 360563120230938062, 360562866928744189, 360562570120122477, 360562273483606601, 360562059430686616]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 3440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 3400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨359987176708940273, 359987176767072213⟩, ⟨1982331305041104360, 1982331441686820636⟩, true⟩

def words05 : List Nat := [360561923859085504, 360561735173814249, 360561546597826692, 360561315947265028, 360561081137630966, 360560824719722278, 360560568450149594, 360560394370110600, 360560270563415673, 360560104929409445]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 3450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 3400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360775272535334686, 360775272593822599⟩, ⟨(-748119625908591092), (-748119488029405804)⟩, true⟩

def words06 : List Nat := [360559939391109454, 360559855812365345, 360559857870094120, 360559899795054046, 360559899795089900, 360559855109421911, 360559728642596402, 360559683925605603, 360559676199538793, 360559738313203353]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 3460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 3400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360407766667325914, 360407766726174863⟩, ⟨529430766766485463, 529430905900243447⟩, true⟩

def words07 : List Nat := [360559745484024127, 360559752650720046, 360559789702904190, 360559869713613016, 360559923445561211, 360559977146608626, 360559977146642487, 360559975296922944, 360559945773530582, 360559902043962290]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 3470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 3400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360137295749568306, 360137295808774720⟩, ⟨1471513575093408583, 1471513715472967153⟩, true⟩

def words08 : List Nat := [360559872454508207, 360559872454546112, 360559805578777948, 360559690610270771, 360559575707736520, 360559399498293860, 360559286188822258, 360559182217564673, 360559078305902464, 360558932976532018]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 3480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 3400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360445794110695681, 360445794170262190⟩, ⟨392210371205122168, 392210512843222678⟩, true⟩

def words09 : List Nat := [360558812198227828, 360558772120149535, 360558732065008206, 360558688276290595, 360558564008247142, 360558369190591874, 360558174484349376, 360557998688211649, 360557886343083827, 360557854316788826]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 3490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 3400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 3400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk034
