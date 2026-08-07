import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk528

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575880023157730, 360575897590236701⟩, ⟨322328643637576113, 322955359498784967⟩, true⟩

def state01 : KState := ⟨⟨360568399229548751, 360568416803526011⟩, ⟨717260698727952739, 717887778853603795⟩, true⟩

def words00 : List Nat := [360582014053776264, 360582013811484293, 360582013450957903, 360582012911141927, 360582012371226901, 360582011666810292, 360582011184991957, 360582011061217451, 360582010937354287, 360582010588393529]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 52800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 52800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577875381126526, 360577892962011864⟩, ⟨216757565613460904, 217385010588898680⟩, true⟩

def words01 : List Nat := [360582010331584958, 360582010129500793, 360582010082118808, 360582010082850873, 360582009880789075, 360582009341726934, 360582008802545056, 360582008621351248, 360582008620590655, 360582008543431571]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 52810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 52800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580854362609175, 360580871950478487⟩, ⟨59362148925294960, 59989962828479944⟩, true⟩

def words02 : List Nat := [360582008466174320, 360582008209885955, 360582008322773864, 360582008511468573, 360582008607042351, 360582008607774745, 360582008462253645, 360582008137509229, 360582007812646991, 360582007478830342]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 52820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 52800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360548633958182860, 360548651552950526⟩, ⟨1761754665847658207, 1762382844224957297⟩, true⟩

def words03 : List Nat := [360582007603083393, 360582007748967388, 360582007749624196, 360582007624266502, 360582007141424674, 360582006568875467, 360582005996116710, 360582005780977706, 360582005378802067, 360582004748337070]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 52830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 52800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572319390143599, 360572336991833835⟩, ⟨510058629029719627, 510687173229873691⟩, true⟩

def words04 : List Nat := [360582004117730270, 360582003731202425, 360582003524805979, 360582003309457777, 360582003094058997, 360582002572682282, 360582001693997523, 360582001041652357, 360582000389109948, 360581999946861837]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 52840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 52800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360573342276060004, 360573359884724774⟩, ⟨455916951216158660, 456545864054845392⟩, true⟩

def words05 : List Nat := [360581999764680716, 360581999366063803, 360581998967323266, 360581998688307861, 360581998639820237, 360581998337469329, 360581998035067418, 360581997454543268, 360581996934610156, 360581996772050822]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 52850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 52800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580717239895435, 360580734855458100⟩, ⟨65979786415456577, 66609063911212929⟩, true⟩

def words06 : List Nat := [360581996802969773, 360581996803702534, 360581996641021460, 360581996258259331, 360581995875379486, 360581995341682199, 360581995086487305, 360581995024166622, 360581994961768376, 360581994720483847]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 52860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 52800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571571276303624, 360571588898793294⟩, ⟨549438669737282998, 550068313498190246⟩, true⟩

def words07 : List Nat := [360581994697260804, 360581994507941153, 360581994329750944, 360581994330483893, 360581993985575331, 360581993331171024, 360581992676657313, 360581991847324133, 360581991294326146, 360581991098367769]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 52870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 52800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565403518720298, 360565421148187690⟩, ⟨875453113798353047, 876083126574716387⟩, true⟩

def words08 : List Nat := [360581990902311176, 360581990527467274, 360581989888844803, 360581989607274848, 360581989325520761, 360581988797614956, 360581988062712379, 360581987055247632, 360581986047675744, 360581985397130302]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 52880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 52800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360517167360326582, 360517184996708439⟩, ⟨3427051187540662446, 3427681566057092966⟩, true⟩

def words09 : List Nat := [360581985084545992, 360581985049214318, 360581985013797972, 360581984799682775, 360581984346606449, 360581983734267204, 360581983121736600, 360581982595957397, 360581981713580295, 360581980489450540]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 52890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 52800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 52800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk528
