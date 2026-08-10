import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk427A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576646151253952, 360576657442118051⟩, ⟨257334513578327640, 257660334449870742⟩, true⟩

def state01 : KState := ⟨⟨360633765539901987, 360633776836254068⟩, ⟨(-2181860724381271822), (-2181534669145569938)⟩, true⟩

def words00 : List Nat := [360582691908133734, 360582692731393532, 360582694102708719, 360582695474072609, 360582696383034237, 360582696909360607, 360582697421099673, 360582697932977114, 360582698992777916, 360582700189274471]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 42700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 42700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360645837950380319, 360645849252274998⟩, ⟨(-2697647408526892046), (-2697321116540032780)⟩, true⟩

def words01 : List Nat := [360582701038235310, 360582701887220424, 360582702790888758, 360582704108109676, 360582705284070678, 360582706460071656, 360582707303129301, 360582708233875857, 360582709712366601, 360582711190981021]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 42710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 42700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360630830377133287, 360630841684513192⟩, ⟨(-2056599823030536011), (-2056273296686915333)⟩, true⟩

def words02 : List Nat := [360582712426764379, 360582713354929968, 360582713938577654, 360582714522260411, 360582714968016415, 360582715686887756, 360582716953298997, 360582718219772598, 360582719210316362, 360582720337091253]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 42720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 42700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360666875642037398, 360666886954913161⟩, ⟨(-3597146393329798352), (-3596819632121358528)⟩, true⟩

def words03 : List Nat := [360582721382659007, 360582722428351105, 360582723904372309, 360582725135235850, 360582725771508642, 360582726407783995, 360582727591421939, 360582729167458659, 360582731136993519, 360582733106567981]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 42730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 42700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360686275647222691, 360686286965659666⟩, ⟨(-4426431618854118541), (-4426104619933470777)⟩, true⟩

def words04 : List Nat := [360582734800760416, 360582736693321696, 360582739133023091, 360582741572784001, 360582743788637827, 360582746170814034, 360582748277239978, 360582750383630960, 360582752353994586, 360582754776472666]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 42740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 42700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk427A
