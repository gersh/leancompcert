import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk328A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk328A
