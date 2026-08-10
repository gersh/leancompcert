import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk262A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk262B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk262A

def state06 : KState := ⟨⟨360495692427501288, 360495696527648208⟩, ⟨2287666745099432827, 2287739577188069617⟩, true⟩

def words05 : List Nat := [360582822922012317, 360582824714470483, 360582825786378156, 360582825786722337, 360582825413034372, 360582824310366800, 360582823207689682, 360582821227505847, 360582818640744360, 360582815323428409]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360624919839928043, 360624923943324129⟩, ⟨(-1106484764835200741), (-1106411847407413523)⟩, true⟩

def words06 : List Nat := [360582812006285935, 360582810135879222, 360582809326285437, 360582809644852907, 360582809645171319, 360582808526283359, 360582806787269576, 360582806494365948, 360582807009301509, 360582808612830147]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360590074299420602, 360590078406104744⟩, ⟨(-191000283238721731), (-190927279417770607)⟩, true⟩

def words07 : List Nat := [360582809101830994, 360582809590823678, 360582809913934999, 360582811173075530, 360582812057933612, 360582812942780039, 360582812953019168, 360582813011789732, 360582813288531395, 360582813565367414]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605119685675778, 360605123795604614⟩, ⟨(-586558868508956266), (-586485779401118164)⟩, true⟩

def words08 : List Nat := [360582814666469431, 360582815311036348, 360582815311343514, 360582815226583320, 360582815141778530, 360582814058198445, 360582814759991528, 360582815601879258, 360582815602189743, 360582816322347564]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360630389911256342, 360630394024443283⟩, ⟨(-1250932295832130434), (-1250859121052434246)⟩, true⟩

def words09 : List Nat := [360582818138174518, 360582819953970381, 360582823212288311, 360582825029270466, 360582825627157087, 360582826225025840, 360582828265289687, 360582831032011438, 360582832840776141, 360582834649474559]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk262B
