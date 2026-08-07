import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk962

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360605467825201280, 360605528972029832⟩, ⟨(-2240818042941351066), (-2236846030433565320)⟩, true⟩

def state01 : KState := ⟨⟨360591633526900121, 360591694687043277⟩, ⟨(-909974823507687256), (-906001530069485300)⟩, true⟩

def words00 : List Nat := [360582277335819706, 360582277412788988, 360582277526014958, 360582277639645530, 360582277709567552, 360582277762976310, 360582277764219318, 360582277763286171, 360582277769002761, 360582277868487504]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 96200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 96200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360566794061769055, 360566855235045570⟩, ⟨1480022606278452723, 1483997163344666385⟩, true⟩

def words01 : List Nat := [360582278075545148, 360582278282866395, 360582278422674196, 360582278482359934, 360582278483548156, 360582278469927335, 360582278457155724, 360582278458551431, 360582278353389526, 360582278194548217]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 96210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 96200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590369826655846, 360590431013129367⟩, ⟨(-788479523628594212), (-784503696683366016)⟩, true⟩

def words02 : List Nat := [360582278035389411, 360582278022980297, 360582278170413174, 360582278318111909, 360582278373138031, 360582278396272292, 360582278483427680, 360582278571017485, 360582278629925152, 360582278716087007]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 96220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 96200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575073435104688, 360575134634866754⟩, ⟨683634260289455448, 687611366057596576⟩, true⟩

def words03 : List Nat := [360582278747706038, 360582278779479036, 360582278918992178, 360582279124939066, 360582279279610249, 360582279434528468, 360582279502447205, 360582279503843160, 360582279464019064, 360582279391371925]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 96230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 96200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580386526892179, 360580447739811688⟩, ⟨172212093588322786, 176190465694663178⟩, true⟩

def words04 : List Nat := [360582279330530169, 360582279331926200, 360582279237840102, 360582279060872706, 360582278883681075, 360582278679348134, 360582278529287536, 360582278467686898, 360582278405934617, 360582278290104620]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 96240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 96200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk962
