import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk512

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496700003296225, 362496737954326942⟩, ⟨(-600923222437509656), (-599610505779916458)⟩, true⟩

def state01 : KState := ⟨⟨362470725714423412, 362470763680895711⟩, ⟨729044196410885607, 730357703756855229⟩, true⟩

def words00 : List Nat := [371285027268837086, 371285027270549009, 371285027090979958, 371285027193068151, 371285027253666184, 371285027255378248, 371285026808134916, 371285026340547908, 371285025872268566, 371285025694247730]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 51200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 51200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362461757994207829, 362461795976108204⟩, ⟨1188426989535668969, 1189741287030970897⟩, true⟩

def words01 : List Nat := [371285025482150583, 371285025549259284, 371285025595873851, 371285025597587645, 371285025231135834, 371285024982648801, 371285024863307730, 371285024865020113, 371285024488748139, 371285024037159180]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 51210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 51200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478633347794986, 362478671345014104⟩, ⟨323988630237473319, 325303712438702305⟩, true⟩

def words02 : List Nat := [371285023584839403, 371285023275392290, 371285022774818961, 371285022631231855, 371285022487100826, 371285022291588974, 371285021779249434, 371285021463902075, 371285021210748641, 371285021212522180]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 51220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 51200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485982825444173, 362486020838308085⟩, ⟨(-52603503642644510), (-51287619880451756)⟩, true⟩

def words03 : List Nat := [371285021089857450, 371285020968273961, 371285020846001713, 371285020808709366, 371285020580379630, 371285020469819771, 371285020358714565, 371285020246851646, 371285019906784726, 371285019928492109]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 51230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 51200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362469141907146296, 362469179935270714⟩, ⟨810468233902898528, 811784899692321392⟩, true⟩

def words04 : List Nat := [371285020329458043, 371285020331171285, 371285020225066223, 371285020110680233, 371285019995657445, 371285019949223168, 371285019772069375, 371285019753195970, 371285019733732389, 371285019640630565]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 51240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 51200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362503866349290772, 362503904392875600⟩, ⟨(-969310449929896646), (-967992991714580630)⟩, true⟩

def words05 : List Nat := [371285019344614411, 371285019358526599, 371285019716084686, 371285019761253728, 371285019762596567, 371285019689603033, 371285019921045749, 371285020037931036, 371285020407503140, 371285020777813183]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 51250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 51200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492016559640289, 362492054618700761⟩, ⟨(-361879274008366678), (-360561022433007306)⟩, true⟩

def words06 : List Nat := [371285021074514920, 371285021076232681, 371285021323382812, 371285021638428371, 371285022069556237, 371285022071270132, 371285021995767813, 371285021894096738, 371285022024149451, 371285022163269172]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 51260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 51200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362468079075981566, 362468117150482669⟩, ⟨865562044434195803, 866881087729726591⟩, true⟩

def words07 : List Nat := [371285022425527039, 371285022688493350, 371285022945813665, 371285022947529222, 371285022775668192, 371285022631390229, 371285022662658273, 371285022664372625, 371285022335603848, 371285022007887695]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 51270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 51200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481688370318567, 362481726460190412⟩, ⟨167712728647311783, 169032560232492153⟩, true⟩

def words08 : List Nat := [371285021679402425, 371285021631622919, 371285021706244243, 371285021934609749, 371285022128884554, 371285022130599106, 371285021884612489, 371285021952873379, 371285022082515833, 371285022084293210]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 51280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 51200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485073540610171, 362485111646108871⟩, ⟨(-5933643504931342), (-4613010341633874)⟩, true⟩

def words09 : List Nat := [371285022021334865, 371285021929833894, 371285021939936949, 371285021941826649, 371285021926100022, 371285021978118894, 371285022030044128, 371285022031767282, 371285021721747542, 371285021725632826]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 51290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 51200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 51200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk512
