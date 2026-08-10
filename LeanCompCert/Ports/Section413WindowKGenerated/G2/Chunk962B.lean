import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk962A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk962B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk962A

def state06 : KState := ⟨⟨360602645336602947, 360602706562690624⟩, ⟨(-1970331170534152828), (-1966351530927312992)⟩, true⟩

def words05 : List Nat := [360582278311112684, 360582278351554975, 360582278472407855, 360582278612773562, 360582278655442282, 360582278698203168, 360582278738135635, 360582278843945465, 360582279057287867, 360582279270942904]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 96250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 96200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595305680067702, 360595366919445383⟩, ⟨(-1263889551760799168), (-1259908632791259880)⟩, true⟩

def words06 : List Nat := [360582279403540936, 360582279428694178, 360582279561519176, 360582279694793228, 360582279768529672, 360582279769926112, 360582279760849697, 360582279697629879, 360582279677457719, 360582279814992420]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 96260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 96200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582568914902438, 360582630167452353⟩, ⟨(-37703542385200961), (-33721355260952601)⟩, true⟩

def words07 : List Nat := [360582279905556982, 360582279996374162, 360582280019350992, 360582280020748227, 360582279981525961, 360582279915436645, 360582279850139781, 360582279918546803, 360582279923428680, 360582279928513612]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 96270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 96200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360604287534038892, 360604348799760871⟩, ⟨(-2128885712716069125), (-2124902257319689965)⟩, true⟩

def words08 : List Nat := [360582280041185502, 360582280208102724, 360582280390971321, 360582280574096321, 360582280653430258, 360582280667956187, 360582280763456846, 360582280859370220, 360582281062752431, 360582281293375854]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 96280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 96200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360600183719905068, 360600244998956388⟩, ⟨(-1733673937148900466), (-1729689198205623294)⟩, true⟩

def words09 : List Nat := [360582281454147316, 360582281615077921, 360582281883588706, 360582282235342660, 360582282559198540, 360582282883275797, 360582283152938338, 360582283343447115, 360582283531113404, 360582283719237532]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 96290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 96200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 96200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk962B
