import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk697A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk697B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk697A

def state06 : KState := ⟨⟨360527879354920147, 360527910711169055⟩, ⟨3816437951849487578, 3817915475589146208⟩, true⟩

def words05 : List Nat := [360582645091003991, 360582644799048914, 360582644506994688, 360582644112539198, 360582643512652144, 360582642769447667, 360582642025974911, 360582641436381686, 360582640787636123, 360582640004110414]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 69750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 69700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360561319259109651, 360561350624696205⟩, ⟨1483598289311556955, 1485076464490664261⟩, true⟩

def words06 : List Nat := [360582639220383410, 360582638641903950, 360582638260599518, 360582638084398269, 360582637908125368, 360582637556583339, 360582636999642739, 360582636647913535, 360582636295902110, 360582635940225669]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 69760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 69700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360556045169916290, 360556076544904440⟩, ⟨1851564410868485041, 1853043242044513017⟩, true⟩

def words07 : List Nat := [360582635636036154, 360582635203333849, 360582634770460262, 360582634370143039, 360582634096195834, 360582633770280588, 360582633444257747, 360582633015423582, 360582632430821627, 360582632051382579]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 69770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 69700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360561393451972553, 360561424836284341⟩, ⟨1478317287363125253, 1479796769188681277⟩, true⟩

def words08 : List Nat := [360582631671627028, 360582631415819302, 360582631186939812, 360582630797938273, 360582630408777548, 360582629895938758, 360582629485601820, 360582629165982461, 360582628846264876, 360582628400823512]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 69780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 69700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360564782752672141, 360564814146303951⟩, ⟨1241758217157219978, 1243238349473404790⟩, true⟩

def words09 : List Nat := [360582628097807379, 360582627949681359, 360582627801269798, 360582627799924753, 360582627593445823, 360582627183807052, 360582626774008842, 360582626254509509, 360582625838133198, 360582625583975490]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 69790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 69700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 69700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk697B
