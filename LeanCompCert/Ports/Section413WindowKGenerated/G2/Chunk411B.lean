import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk411A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk411B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk411A

def state06 : KState := ⟨⟨360562944409439811, 360562954869081215⟩, ⟨796848363310850693, 797139326785744281⟩, true⟩

def words05 : List Nat := [360582326099728510, 360582325599487911, 360582325099172579, 360582324585835380, 360582324428130758, 360582324119929846, 360582323811688997, 360582323082861239, 360582322183644250, 360582321713755310]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 41150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 41100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578533254548549, 360578543719449150⟩, ⟨155164918535201501, 155456098505755811⟩, true⟩

def words06 : List Nat := [360582321361849349, 360582321395389013, 360582321395887159, 360582321134148599, 360582320872331467, 360582320460319647, 360582320347434383, 360582320221720718, 360582320095951810, 360582319675205909]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 41160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 41100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360629477552014327, 360629488022193107⟩, ⟨(-1942621895772827070), (-1942330498474098778)⟩, true⟩

def words07 : List Nat := [360582319662648192, 360582319741962458, 360582319742418731, 360582319864264205, 360582319864785812, 360582319539732586, 360582319477132894, 360582320035089040, 360582321180951417, 360582322326885220]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 41170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 41100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360620255841252532, 360620266316764905⟩, ⟨(-1563059186122870006), (-1562767569160003530)⟩, true⟩

def words08 : List Nat := [360582322964341234, 360582323235617256, 360582324094766532, 360582324954050617, 360582325663044110, 360582325785289684, 360582325785788151, 360582325613343400, 360582325855598908, 360582326777322794]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 41180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 41100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360545308216314860, 360545318697094544⟩, ⟨1524509363425797106, 1524801197375502272⟩, true⟩

def words09 : List Nat := [360582327899187087, 360582329021103903, 360582329778049015, 360582330171743225, 360582330172222882, 360582330023755100, 360582329896603366, 360582329897162983, 360582329332631429, 360582328434894921]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 41190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 41100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 41100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk411B
