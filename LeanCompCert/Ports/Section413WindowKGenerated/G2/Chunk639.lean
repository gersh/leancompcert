import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk639

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

def state06 : KState := ⟨⟨360610174312349627, 360610200489580074⟩, ⟨(-1753244230508384788), (-1752113209206844378)⟩, true⟩

def words05 : List Nat := [360582801749649226, 360582802191628623, 360582802779433118, 360582803595366570, 360582804349108977, 360582805102974742, 360582805733731254, 360582806169430095, 360582806598473925, 360582807027795443]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 63950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 63900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360605101553967338, 360605127739660884⟩, ⟨(-1428804699630888808), (-1427673136985968526)⟩, true⟩

def words06 : List Nat := [360582807651541544, 360582808032252354, 360582808249412109, 360582808466653803, 360582808524180519, 360582808771656044, 360582809183493782, 360582809595490694, 360582809884470177, 360582810234275851]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 63960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 63900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606489703528234, 360606515897728578⟩, ⟨(-1517752018880864303), (-1516619912014190245)⟩, true⟩

def words07 : List Nat := [360582810572440844, 360582810910866140, 360582811062887293, 360582811083585552, 360582811084416188, 360582810894001909, 360582810756267639, 360582810931736890, 360582811302970303, 360582811674412060]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 63970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 63900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601810619917702, 360601836822694435⟩, ⟨(-1218499350670093134), (-1217366695045822254)⟩, true⟩

def words08 : List Nat := [360582811924097699, 360582811930843882, 360582812130803489, 360582812331021850, 360582812430653256, 360582812574373007, 360582812575194201, 360582812491260571, 360582812494496223, 360582812792830145]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 63980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 63900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360604511481809492, 360604537693059095⟩, ⟨(-1391293761420655910), (-1390160563574128470)⟩, true⟩

def words09 : List Nat := [360582813275016281, 360582813757361554, 360582814104721956, 360582814462000952, 360582814757311098, 360582815052850463, 360582815592103052, 360582816093107235, 360582816433320496, 360582816773642616]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 63990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 63900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 63900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk639
