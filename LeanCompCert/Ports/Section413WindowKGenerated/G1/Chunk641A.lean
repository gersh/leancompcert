import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk641A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362510991740741365, 362511052299703269⟩, ⟨(-1640588374512020780), (-1637966464904969300)⟩, true⟩

def state01 : KState := ⟨⟨362503216392324267, 362503276970945451⟩, ⟨(-1142226262749312943), (-1139603092880440073)⟩, true⟩

def words00 : List Nat := [371285499778454357, 371285499833727567, 371285500047698635, 371285500262804643, 371285500550423729, 371285500683088983, 371285500781448775, 371285500880520279, 371285501222196473, 371285501501948237]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 64100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 64100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484294045937145, 362484354644240997⟩, ⟨71058503264522124, 73682935088665682⟩, true⟩

def words01 : List Nat := [371285501987678989, 371285502474309730, 371285502901051187, 371285503004076662, 371285503180111708, 371285503357231845, 371285503739972671, 371285503799228612, 371285503800871642, 371285503785461969]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 64110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 64100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362493163274551125, 362493223892374708⟩, ⟨(-497631199298729867), (-495005515772104321)⟩, true⟩

def words02 : List Nat := [371285503941139794, 371285503994514733, 371285504290311115, 371285504586976289, 371285504857988925, 371285504860169845, 371285504852637679, 371285504901037404, 371285505107694126, 371285505230327148]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 64120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 64100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495358681614989, 362495419319251376⟩, ⟨(-638404457511653816), (-635777503285933294)⟩, true⟩

def words03 : List Nat := [371285505351575582, 371285505473536664, 371285505793840624, 371285506028017956, 371285506307051864, 371285506586931401, 371285506865322692, 371285506867503825, 371285506976330109, 371285507133546664]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 64130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 64100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477936874101544, 362477997531196848⟩, ⟨479102870445485220, 481731072866824878⟩, true⟩

def words04 : List Nat := [371285507275741193, 371285507277932914, 371285507188518635, 371285507100607961, 371285507011831129, 371285506997571523, 371285506898667190, 371285506938413472, 371285506976681478, 371285506978942239]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 64140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 64100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk641A
