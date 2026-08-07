import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk865

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470709946592776, 362470822820879128⟩, ⟨1237700127792859414, 1244292589562636184⟩, true⟩

def state01 : KState := ⟨⟨362488049487995911, 362488162389212063⟩, ⟨(-262227730753060304), (-255632939421308090)⟩, true⟩

def words00 : List Nat := [371285207542050172, 371285207512629723, 371285207444708584, 371285207460950130, 371285207464327091, 371285207467390167, 371285207376420076, 371285207352702056, 371285207433611139, 371285207470884668]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 86500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 86500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480353696248256, 362480466624935922⟩, ⟨403570417774443775, 410167585804159897⟩, true⟩

def words01 : List Nat := [371285207507414162, 371285207544999275, 371285207604159094, 371285207607475269, 371285207599931057, 371285207592381795, 371285207583863100, 371285207576130439, 371285207401587797, 371285207350615582]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 86510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 86500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473332467163012, 362473445422665169⟩, ⟨1011095227171779883, 1017694715323719199⟩, true⟩

def words02 : List Nat := [371285207356001541, 371285207359010978, 371285207241372328, 371285207121309278, 371285207000125109, 371285206919629914, 371285206807515407, 371285206738885430, 371285206669180668, 371285206600468518]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 86520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 86500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362496746027750150, 362496859010382334⟩, ⟨(-1014980589358109562), (-1008378753502429516)⟩, true⟩

def words03 : List Nat := [371285206466590666, 371285206467689710, 371285206598231728, 371285206621735514, 371285206624088468, 371285206626818186, 371285206696245727, 371285206700783918, 371285206837471295, 371285206975468219]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 86530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 86500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478880976405098, 362478993986253496⟩, ⟨531120793470043931, 537724984753507325⟩, true⟩

def words04 : List Nat := [371285207093054884, 371285207096064977, 371285207076523837, 371285207121278864, 371285207194635297, 371285207197645684, 371285207109755272, 371285207006994047, 371285206902961535, 371285206868804086]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 86540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 86500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362468538811791762, 362468651848742519⟩, ⟨1426341160790438483, 1432947697923017243⟩, true⟩

def words05 : List Nat := [371285206828754754, 371285206861742227, 371285206878503633, 371285206881528563, 371285206770533318, 371285206667807062, 371285206571478071, 371285206574488917, 371285206423094082, 371285206235271205]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476352812523331, 362476465876466332⟩, ⟨749981114995295926, 756589988712902802⟩, true⟩

def words06 : List Nat := [371285206046067404, 371285205991598444, 371285205900095799, 371285205916275043, 371285205918606863, 371285205917190080, 371285205736968970, 371285205646898032, 371285205555276254, 371285205509003157]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484315479819160, 362484428571179730⟩, ⟨60624091226212472, 67235338617805962⟩, true⟩

def words07 : List Nat := [371285205410321549, 371285205312646812, 371285205246173598, 371285205249493279, 371285205244464153, 371285205264000281, 371285205282555240, 371285205285567161, 371285205145335004, 371285205140117335]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474769057401769, 362474882175592788⟩, ⟨887168397554590525, 893781968067994847⟩, true⟩

def words08 : List Nat := [371285205157327552, 371285205160339180, 371285205008970724, 371285204842104681, 371285204674060883, 371285204548011950, 371285204354034678, 371285204294540598, 371285204234081025, 371285204175454990]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488591977780583, 362488705123229651⟩, ⟨(-309824358819475475), (-303208427898542685)⟩, true⟩

def words09 : List Nat := [371285204062620486, 371285204070623704, 371285204165553123, 371285204168567812, 371285204118749690, 371285204037491382, 371285203955071729, 371285203918098556, 371285203867759221, 371285203911605091]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk865
