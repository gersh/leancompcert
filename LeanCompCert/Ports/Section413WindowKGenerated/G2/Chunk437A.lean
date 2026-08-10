import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk437A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360625294563330615, 360625306411732886⟩, ⟨(-1840328465785913670), (-1839978558145977088)⟩, true⟩

def state01 : KState := ⟨⟨360594145531727632, 360594157385819290⟩, ⟨(-479246504310045495), (-478896348015970599)⟩, true⟩

def words00 : List Nat := [360583203161493790, 360583203198326363, 360583203198812483, 360583203106821036, 360583203014669934, 360583202788850194, 360583202554474737, 360583201953288074, 360583201352004342, 360583201417115395]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 43700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 43700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569342742981336, 360569354602688461⟩, ⟨605165721957440326, 605516123732506554⟩, true⟩

def words01 : List Nat := [360583202191073889, 360583202965111225, 360583203479865222, 360583203922850128, 360583204007103530, 360583204091502385, 360583204698456595, 360583204783921155, 360583204784456620, 360583204468281611]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 43710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 43700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597664787196971, 360597676652545165⟩, ⟨(-633084931767357893), (-632734283336801343)⟩, true⟩

def words02 : List Nat := [360583204357868842, 360583204982650586, 360583205849115981, 360583206715656926, 360583207076005579, 360583207076602572, 360583207127738582, 360583207340695477, 360583207539571042, 360583207871055220]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 43720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 43700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603401926435535, 360603413797474484⟩, ⟨(-884017507671305954), (-883666610356946168)⟩, true⟩

def words03 : List Nat := [360583207897892182, 360583207924791284, 360583208331064609, 360583209068211528, 360583209671559095, 360583210274990873, 360583210559771798, 360583210622697752, 360583211085073070, 360583211547632072]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 43730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 43700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360561678382228197, 360561690258899600⟩, ⟨941037147724690128, 941388291430781810⟩, true⟩

def words04 : List Nat := [360583211984637757, 360583211985235013, 360583211901228219, 360583211413346261, 360583210925391636, 360583210155620599, 360583209718939101, 360583209135842057, 360583208552711408, 360583207705560876]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 43740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 43700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk437A
