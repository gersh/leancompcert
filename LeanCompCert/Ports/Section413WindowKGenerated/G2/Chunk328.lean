import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk328

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360568804786472434, 360568811306186371⟩, ⟨409435117590800990, 409579714102549292⟩, true⟩

def state01 : KState := ⟨⟨360644412412379018, 360644418936227985⟩, ⟨(-2070681005225288146), (-2070536273064786954)⟩, true⟩

def words00 : List Nat := [360581298658607955, 360581300105754926, 360581302479647253, 360581304853478642, 360581306437596286, 360581307443223813, 360581309074989547, 360581310706783763, 360581312069785884, 360581313993584824]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 32800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 32800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360610083342934546, 360610089870950166⟩, ⟨(-944217411064775155), (-944072542175137529)⟩, true⟩

def words01 : List Nat := [360581315451795132, 360581316909966431, 360581318085374541, 360581319728462761, 360581321135359696, 360581322542249794, 360581323483930213, 360581323833892982, 360581324710726193, 360581325587650598]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 32810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 32800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581023532880500, 360581030065026086⟩, ⟨9505861153843220, 9650865609426708⟩, true⟩

def words02 : List Nat := [360581326878126192, 360581327242764745, 360581327243165211, 360581326883176101, 360581326523136835, 360581325573629069, 360581325092484261, 360581324916200490, 360581324739879614, 360581324029863413]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 32820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 32800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360631438325186120, 360631444861464188⟩, ⟨(-1645890571445392465), (-1645745431299407807)⟩, true⟩

def words03 : List Nat := [360581324937547624, 360581325854263866, 360581327695971292, 360581328612456972, 360581328644009443, 360581328675591605, 360581328681954816, 360581329283711309, 360581330810118603, 360581332336531957]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 32830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 32800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360632909498190657, 360632916038643905⟩, ⟨(-1694507429210999880), (-1694362151932231444)⟩, true⟩

def words04 : List Nat := [360581333254391594, 360581333254829757, 360581334164784768, 360581335082346743, 360581335764867764, 360581336317665394, 360581336406551796, 360581336495480626, 360581337281611679, 360581338852198067]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 32840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 32800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk328
