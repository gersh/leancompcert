import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk328A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk328B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk328A

def state06 : KState := ⟨⟨360535455482015749, 360535462026600910⟩, ⟨1507281054691793067, 1507426467724749139⟩, true⟩

def words05 : List Nat := [360581339866473293, 360581340880762186, 360581341347455796, 360581341347894094, 360581340890267636, 360581340198398177, 360581339506445119, 360581338552830862, 360581337630021726, 360581336234383161]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 32850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 32800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580137286281123, 360580143835004959⟩, ⟨38745065712396596, 38890614762631478⟩, true⟩

def words06 : List Nat := [360581334838731028, 360581333748288098, 360581333125267502, 360581333092864561, 360581333060434273, 360581332153925211, 360581330323865217, 360581328908042750, 360581327492170544, 360581326999433394]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 32860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 32800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360545129809903719, 360545136362807884⟩, ⟨1189754786090898262, 1189900472569645702⟩, true⟩

def words07 : List Nat := [360581326963829967, 360581326465380596, 360581326118755858, 360581326738071327, 360581327079919343, 360581327421817610, 360581327422213836, 360581327180773671, 360581326650107815, 360581325549929832]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 32870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 32800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591451486900639, 360591458043937460⟩, ⟨(-333688711486695483), (-333542889106364779)⟩, true⟩

def words08 : List Nat := [360581324449673743, 360581324036351074, 360581323109009526, 360581321627274026, 360581320145557183, 360581318430706097, 360581317495695632, 360581317482662406, 360581317469582989, 360581317188107405]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 32880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 32800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360599028503556672, 360599035064736977⟩, ⟨(-583096717447556636), (-582950758767803972)⟩, true⟩

def words09 : List Nat := [360581318046138397, 360581318904245346, 360581319441876327, 360581319442315237, 360581319058185855, 360581317769882537, 360581316481573708, 360581315836751143, 360581316196226646, 360581316735240372]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 32890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 32800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 32800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk328B
