import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk261A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk261B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk261A

def state06 : KState := ⟨⟨360539097064815720, 360539101132456853⟩, ⟨1144537815738587665, 1144609795849992995⟩, true⟩

def words05 : List Nat := [360582869191255581, 360582866405046345, 360582863618979000, 360582862291544853, 360582861714067128, 360582860761396640, 360582859808760188, 360582858119149022, 360582857001780198, 360582855329545921]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360547932173714331, 360547936244586183⟩, ⟨913384802555430268, 913456867198257256⟩, true⟩

def words06 : List Nat := [360582853657326410, 360582853442754218, 360582852275824399, 360582849995740730, 360582847715775362, 360582845061530186, 360582843563997519, 360582843129100680, 360582842694203340, 360582840977761509]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360617227355704516, 360617231429819619⟩, ⟨(-900514046287431406), (-900441896752647552)⟩, true⟩

def words07 : List Nat := [360582839766884048, 360582839889818703, 360582839974276564, 360582839974620221, 360582839439235407, 360582837630936471, 360582835822710300, 360582835848874245, 360582837162963445, 360582838477038876]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360637458277427228, 360637462354811248⟩, ⟨(-1430453527597692756), (-1430381292466646864)⟩, true⟩

def words08 : List Nat := [360582839067124644, 360582840026456195, 360582842440507554, 360582844854474681, 360582846895135427, 360582847483135776, 360582847483447400, 360582846771987736, 360582846802966509, 360582848888640936]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360527564405319391, 360527568485937306⟩, ⟨1448439058774418800, 1448511378617481072⟩, true⟩

def words09 : List Nat := [360582851190736134, 360582853492719197, 360582855060030507, 360582856678516928, 360582857362542226, 360582858046604553, 360582858393598556, 360582858393942056, 360582857289681565, 360582855179777668]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk261B
