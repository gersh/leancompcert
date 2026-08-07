import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk091

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360385246565963411, 360385247012180016⟩, ⟨1735963269545237538, 1735966022451007968⟩, true⟩

def state01 : KState := ⟨⟨360613620979126769, 360613621426371312⟩, ⟨(-343271358933527684), (-343268596668402982)⟩, true⟩

def words00 : List Nat := [360575991548303091, 360575975559474064, 360575973460442959, 360575978399140984, 360575978399241351, 360575972930536069, 360575962272378651, 360575951194660896, 360575941009500236, 360575945145318914]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 9100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 9100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360548231528895606, 360548231977178730⟩, ⟨252892546428974474, 252895318160725998⟩, true⟩

def words01 : List Nat := [360575945145416072, 360575943241051375, 360575942721535527, 360575953263127327, 360575960692664480, 360575968120589592, 360575969391483955, 360575969391593131, 360575964767728956, 360575961726977056]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 9110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 9100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360518632254636864, 360518632703949849⟩, ⟨522184325785747380, 522187106914938696⟩, true⟩

def words02 : List Nat := [360575958686857626, 360575955250810501, 360575939929162128, 360575918596479478, 360575897268454907, 360575871791412609, 360575853866100244, 360575847850074731, 360575841835353763, 360575827348737904]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 9120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 9100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360586454463088231, 360586454913431887⟩, ⟨(-97312710080698010), (-97309919536293766)⟩, true⟩

def words03 : List Nat := [360575821085038980, 360575819883497939, 360575829372719903, 360575829372829236, 360575828196775141, 360575815469896955, 360575802745783850, 360575807148754621, 360575808313807175, 360575809478628661]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 9130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 9100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360510993502658277, 360510993954045249⟩, ⟨592232848719742953, 592235648805211013⟩, true⟩

def words04 : List Nat := [360575809478726787, 360575801496114001, 360575793996134939, 360575792383027838, 360575790770243939, 360575782663736244, 360575771378282734, 360575754096230728, 360575736817937382, 360575719161564945]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 9140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 9100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360487574082754577, 360487574535173645⟩, ⟨807105114403140102, 807107923937440816⟩, true⟩

def words05 : List Nat := [360575716866648673, 360575721643730484, 360575721643829093, 360575720388286736, 360575714196511362, 360575704923803657, 360575698218710544, 360575698218820389, 360575696374118840, 360575686753944108]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 9150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 9100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578699979578530, 360578700433034722⟩, ⟨(-28320126825535862), (-28317307786092964)⟩, true⟩

def words06 : List Nat := [360575679348310208, 360575687609268489, 360575687609359704, 360575686700511951, 360575685791854332, 360575674685581105, 360575651818067426, 360575636264995458, 360575620715284383, 360575612731825902]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 9160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 9100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360631249743115688, 360631250197619432⟩, ⟨(-510385352971851967), (-510382524321317599)⟩, true⟩

def words07 : List Nat := [360575612731924661, 360575607025721346, 360575607410595703, 360575622583229491, 360575634343642394, 360575646101510140, 360575647949338381, 360575647949448861, 360575652972621297, 360575659028430747]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 9170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 9100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360639899263201889, 360639899718740920⟩, ⟨(-590028080344264526), (-590025242184364196)⟩, true⟩

def words08 : List Nat := [360575676854533724, 360575682946431613, 360575683090668025, 360575683234886910, 360575683234979744, 360575675270771180, 360575683139305250, 360575692951155601, 360575696754297995, 360575703739828467]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 9180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 9100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360662592311491961, 360662592768073185⟩, ⟨(-799662305014761437), (-799659457271922331)⟩, true⟩

def words09 : List Nat := [360575704723833433, 360575705707654262, 360575712540491491, 360575712540601685, 360575707675214417, 360575692645798154, 360575677619628668, 360575666094113289, 360575673261733723, 360575682708593572]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 9190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 9100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 9100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk091
