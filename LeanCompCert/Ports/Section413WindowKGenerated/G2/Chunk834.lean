import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk834

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360570280818017243, 360570326269459759⟩, ⟨1006665590922071377, 1009225584291261715⟩, true⟩

def state01 : KState := ⟨⟨360590295200603193, 360590340663308814⟩, ⟨(-662619829537670445), (-660058896768624089)⟩, true⟩

def words00 : List Nat := [360582427151522905, 360582427204500114, 360582427205576987, 360582427187788463, 360582427169821570, 360582427054141296, 360582427108445225, 360582427208138656, 360582427235658598, 360582427331772583]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594795111928670, 360594840585939096⟩, ⟨(-1037969611891997254), (-1035407736133264290)⟩, true⟩

def words01 : List Nat := [360582427543688876, 360582427755987063, 360582427990161549, 360582428111977902, 360582428113081722, 360582428108023158, 360582428240087515, 360582428450552031, 360582428600329820, 360582428750356530]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597593727389118, 360597639212808884⟩, ⟨(-1271547057607984088), (-1268984230028124332)⟩, true⟩

def words02 : List Nat := [360582428791939411, 360582428793136466, 360582428824040015, 360582428912131030, 360582428931748273, 360582428998216396, 360582428999282603, 360582428993733909, 360582429044462632, 360582429228150567]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577854151930037, 360577899648636971⟩, ⟨375486617478255996, 378050386802446978⟩, true⟩

def words03 : List Nat := [360582429554984738, 360582429882040501, 360582430085229695, 360582430247063630, 360582430275694875, 360582430304638822, 360582430476767832, 360582430505811289, 360582430506887948, 360582430453847931]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360603184033767057, 360603229541769578⟩, ⟨(-1738133904401033021), (-1735569192516403849)⟩, true⟩

def words04 : List Nat := [360582430466913198, 360582430606362601, 360582430888977363, 360582431171816529, 360582431332361493, 360582431471026280, 360582431541748880, 360582431612814989, 360582431827017562, 360582432077478960]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360598485132609693, 360598530652011107⟩, ⟨(-1345988539369322871), (-1343422876190370453)⟩, true⟩

def words05 : List Nat := [360582432255822048, 360582432434292394, 360582432660633044, 360582432999580313, 360582433302093507, 360582433604794872, 360582433798530598, 360582433849131872, 360582434042968095, 360582434237204307]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 83450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 83400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588395228545928, 360588440759236283⟩, ⟨(-503886140752372193), (-501319535341060565)⟩, true⟩

def words06 : List Nat := [360582434427227678, 360582434542113778, 360582434572863419, 360582434603742579, 360582434604744531, 360582434665764505, 360582434725489858, 360582434785468918, 360582434786535696, 360582434846579899]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 83460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 83400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360600555612144470, 360600601154129183⟩, ⟨(-1518981338049958471), (-1516413789842276831)⟩, true⟩

def words07 : List Nat := [360582435062924019, 360582435279615823, 360582435538900927, 360582435655211890, 360582435656347630, 360582435637769731, 360582435742591940, 360582435939228638, 360582436157802772, 360582436376636793]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 83470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 83400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605334277977185, 360605379831388143⟩, ⟨(-1917973461592238363), (-1915404959468478475)⟩, true⟩

def words08 : List Nat := [360582436523420566, 360582436713532041, 360582436990231196, 360582437267288382, 360582437483637420, 360582437712785922, 360582437843426587, 360582437974191933, 360582438100947594, 360582438377106024]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 83480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 83400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588789735139819, 360588835299817973⟩, ⟨(-536549375361945931), (-533979932483093117)⟩, true⟩

def words09 : List Nat := [360582438731557644, 360582439086229498, 360582439368752506, 360582439538669995, 360582439672359380, 360582439806386804, 360582440083362069, 360582440251665602, 360582440329325185, 360582440407152220]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 83490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 83400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 83400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk834
