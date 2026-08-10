import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk885A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk885B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk885A

def state06 : KState := ⟨⟨360553273617646464, 360553325105837132⟩, ⟨2548649290675073427, 2551728491061379621⟩, true⟩

def words05 : List Nat := [360582140227169878, 360582140063600838, 360582139899793749, 360582139779522769, 360582139722941132, 360582139619438825, 360582139515813379, 360582139314428797, 360582138985405967, 360582138661517591]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 88550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 88500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360544322591662058, 360544374091866974⟩, ⟨3341316949730096985, 3344397214159254557⟩, true⟩

def words06 : List Nat := [360582138337203768, 360582137995650744, 360582137526571568, 360582136982543719, 360582136438297685, 360582135862316084, 360582135364373753, 360582134944858146, 360582134525229018, 360582134024283812]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 88560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 88500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360559732832368673, 360559784344639332⟩, ⟨1976270215242982959, 1979351548391755759⟩, true⟩

def words07 : List Nat := [360582133599009690, 360582133171209823, 360582132743036282, 360582132375241110, 360582131917089575, 360582131349809909, 360582130782298446, 360582130310695499, 360582129950610107, 360582129699667463]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 88570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 88500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360546474141252058, 360546525665669180⟩, ⟨3150695571863598264, 3153777981008456744⟩, true⟩

def words08 : List Nat := [360582129448545750, 360582129133735046, 360582128781986789, 360582128450250907, 360582128118202521, 360582127698687139, 360582127151727489, 360582126516079209, 360582125880200613, 360582125371967955]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 88580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 88500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360531845328010338, 360531896864471530⟩, ⟨4446810729323285717, 4449894205512185749⟩, true⟩

def words09 : List Nat := [360582124971156500, 360582124697825659, 360582124424339089, 360582124087188648, 360582123730323181, 360582123280850418, 360582122830999658, 360582122437566672, 360582121969588538, 360582121404037131]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 88590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 88500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 88500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk885B
