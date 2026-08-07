import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk672

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578640943821104, 360578669954624844⟩, ⟨286499050650451605, 287815938165213415⟩, true⟩

def state01 : KState := ⟨⟨360562312612377315, 360562341632113217⟩, ⟨1383737405001703199, 1385054892801724899⟩, true⟩

def words00 : List Nat := [360582952866930659, 360582952785424365, 360582952482764961, 360582952037929897, 360582951592953182, 360582951092660083, 360582950731676368, 360582950365977844, 360582950000186385, 360582949501370794]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 67200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 67200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360619668697256335, 360619697725935441⟩, ⟨(-2471482689363343614), (-2470164600444462984)⟩, true⟩

def words01 : List Nat := [360582949195523335, 360582949110931174, 360582949161362808, 360582949303876270, 360582949304751232, 360582949258446048, 360582949385645280, 360582949712456634, 360582950259906499, 360582950807555107]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 67210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 67200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360596412747158102, 360596441784897199⟩, ⟨(-908181768701831248), (-906863070727696330)⟩, true⟩

def words02 : List Nat := [360582951131885685, 360582951473845452, 360582951880923940, 360582952288265117, 360582952638111784, 360582952767173935, 360582952785673881, 360582952804293617, 360582952819491135, 360582953021220805]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 67220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 67200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360562202754073295, 360562231800744843⟩, ⟨1392011619837525951, 1393330918384766573⟩, true⟩

def words03 : List Nat := [360582953443470291, 360582953865895410, 360582954164935605, 360582954243181753, 360582954243992130, 360582954125569540, 360582954045275692, 360582954046224879, 360582953864610978, 360582953557413267]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 67230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 67200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567999219944061, 360568028275587240⟩, ⟨1002280194662787923, 1003600096507983379⟩, true⟩

def words04 : List Nat := [360582953250010896, 360582953039752323, 360582952998976830, 360582952992496801, 360582952985943157, 360582952790931220, 360582952374898608, 360582952179905985, 360582951984648055, 360582951697096653]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 67240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 67200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360565740155720401, 360565769220403097⟩, ⟨1154228720149860847, 1155549229946122147⟩, true⟩

def words05 : List Nat := [360582951476036946, 360582951118466493, 360582950760720666, 360582950581869436, 360582950570781198, 360582950504328584, 360582950437767086, 360582950233482611, 360582949808234379, 360582949553884307]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 67250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 67200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578440883467865, 360578469957106237⟩, ⟨299891250973890138, 301212363172926572⟩, true⟩

def words06 : List Nat := [360582949299224128, 360582949265403553, 360582949176109344, 360582948915267534, 360582948654284039, 360582948248593313, 360582947997518021, 360582947922961901, 360582947848306653, 360582947619707292]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 67260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 67200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592791564541973, 360592820647140250⟩, ⟨(-665524449669132201), (-664202734693529365)⟩, true⟩

def words07 : List Nat := [360582947707948089, 360582947863024430, 360582948238405167, 360582948393260369, 360582948394150869, 360582948343285991, 360582948292247964, 360582948282023903, 360582948429528922, 360582948577243942]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 67270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 67200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586525173139967, 360586554264783524⟩, ⟨(-244048099170745301), (-242725775584245651)⟩, true⟩

def words08 : List Nat := [360582948581789335, 360582948582739113, 360582948366558879, 360582948307611853, 360582948248385831, 360582948133828742, 360582947947679256, 360582947593332263, 360582947238809461, 360582947158698249]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 67280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 67200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574664455467994, 360574693556064996⟩, ⟨554054808454078736, 555377734562766312⟩, true⟩

def words09 : List Nat := [360582947208130286, 360582947257729368, 360582947258583647, 360582947196573325, 360582946913833022, 360582946535317476, 360582946156534573, 360582945958620676, 360582945947160022, 360582945825523581]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 67290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 67200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 67200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk672
