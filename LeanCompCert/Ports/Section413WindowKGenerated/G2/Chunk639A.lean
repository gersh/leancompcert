import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk639A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360610519924403017, 360610546050583704⟩, ⟨(-1775805285015382281), (-1774677527325234913)⟩, true⟩

def state01 : KState := ⟨⟨360626196225536866, 360626222360192168⟩, ⟨(-2777676867620321240), (-2776548568359827466)⟩, true⟩

def words00 : List Nat := [360582774434088053, 360582774936637133, 360582775218568191, 360582775500572409, 360582775720443840, 360582776062491812, 360582776649022115, 360582777235710435, 360582777693797944, 360582778374518969]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 63900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 63900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360638584606192089, 360638610749321286⟩, ⟨(-3569475523419658613), (-3568346682550414119)⟩, true⟩

def words01 : List Nat := [360582779235338426, 360582780096394537, 360582781201870839, 360582782063917751, 360582782719287087, 360582783374708711, 360582783946411384, 360582784675874005, 360582785549975206, 360582786424255183]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 63910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 63900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360628761222849204, 360628787374535364⟩, ⟨(-2941674238684216280), (-2940544850810771826)⟩, true⟩

def words02 : List Nat := [360582787085596009, 360582787601060554, 360582788295319197, 360582788989836954, 360582789621171287, 360582790009155659, 360582790275159658, 360582790541246153, 360582791051739234, 360582791772232714]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 63920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 63900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360605035131190273, 360605061291358582⟩, ⟨(-1424752126467867816), (-1423622196287674380)⟩, true⟩

def words03 : List Nat := [360582792485841570, 360582793199593698, 360582793769007631, 360582794265691851, 360582794649079087, 360582795032701657, 360582795498901605, 360582795971176649, 360582796320199882, 360582796669343167]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 63930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 63900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360618851866003222, 360618878034653773⟩, ⟨(-2308273233535069804), (-2307142760958147032)⟩, true⟩

def words04 : List Nat := [360582797172816405, 360582797798288030, 360582798460884688, 360582799123627947, 360582799550545066, 360582799734186145, 360582799988808333, 360582800243683023, 360582800742698260, 360582801307769782]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 63940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 63900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk639A
