import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk704A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586086027042437, 360586117984485838⟩, ⟨(-258045984808807132), (-256526329083340296)⟩, true⟩

def state01 : KState := ⟨⟨360587433203758873, 360587465170689250⟩, ⟨(-353052898792326497), (-351532575135373627)⟩, true⟩

def words00 : List Nat := [360582474197231862, 360582474136689681, 360582473874489261, 360582473707498149, 360582473540247527, 360582473322563356, 360582473155615898, 360582472887562611, 360582472619321301, 360582472590337667]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 70400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 70400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360564756169877460, 360564788146215089⟩, ⟨1243758798923141758, 1245279784991215036⟩, true⟩

def words01 : List Nat := [360582472621357172, 360582472652561795, 360582472653466410, 360582472532021614, 360582472439561207, 360582472296803990, 360582472154369463, 360582472155367099, 360582472005841193, 360582471755771909]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 70410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 70400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593817564821493, 360593849550569287⟩, ⟨(-802877101321314207), (-801355452542438973)⟩, true⟩

def words02 : List Nat := [360582471505469656, 360582471314910282, 360582471472118531, 360582471651884382, 360582471659227739, 360582471660226828, 360582471575301262, 360582471486353038, 360582471508182869, 360582471670764337]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 70420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 70400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360586069710944350, 360586101706196723⟩, ⟨(-257209431659834314), (-255687113427843648)⟩, true⟩

def words03 : List Nat := [360582471691156753, 360582471711655798, 360582471712469746, 360582471810949419, 360582471893956033, 360582471977122993, 360582471978012381, 360582471945453778, 360582471848252385, 360582471900920991]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 70430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 70400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360561556281642460, 360561588286307258⟩, ⟨1469561313975147584, 1471084295265222972⟩, true⟩

def words04 : List Nat := [360582471901742666, 360582471883203021, 360582471663327378, 360582471341249939, 360582471019012392, 360582470619045220, 360582470336584850, 360582470113782266, 360582469890857973, 360582469539611236]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 70440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 70400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk704A
