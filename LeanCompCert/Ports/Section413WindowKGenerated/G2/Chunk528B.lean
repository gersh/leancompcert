import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk528A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk528B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk528A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk528B
