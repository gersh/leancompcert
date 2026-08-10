import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk367A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk367B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk367A

def state06 : KState := ⟨⟨360507235665037583, 360507243931420920⟩, ⟨2734360074541900735, 2734565490762190717⟩, true⟩

def words05 : List Nat := [360581641359453736, 360581641059772027, 360581640760052530, 360581640087101945, 360581639590092886, 360581638905003388, 360581638219808338, 360581637308155238, 360581635657853675, 360581633634651666]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 36750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 36700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591401065996817, 360591409337048426⟩, ⟨(-359926729018252630), (-359721141169386230)⟩, true⟩

def words06 : List Nat := [360581631611447795, 360581630327388480, 360581629620634037, 360581629429672370, 360581629238676772, 360581628432754791, 360581627213883720, 360581626733869258, 360581626330249434, 360581626596813747]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 36760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 36700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593795463224853, 360593803738997070⟩, ⟨(-448155061536229931), (-447949300087820591)⟩, true⟩

def words07 : List Nat := [360581626597263339, 360581626180240641, 360581625763148105, 360581625550948510, 360581625551363147, 360581625452342318, 360581625353275661, 360581624659408242, 360581624583998668, 360581624915689172]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 36770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 36700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608824736487884, 360608833016920136⟩, ⟨(-1001072875906596628), (-1000866943038435982)⟩, true⟩

def words08 : List Nat := [360581625985233935, 360581626589845412, 360581626697780545, 360581626805764104, 360581626806185548, 360581626409812493, 360581627098111855, 360581627811452259, 360581628152500996, 360581628892459305]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 36780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 36700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360636547217602541, 360636555502713850⟩, ⟨(-2021054691929511107), (-2020848586895608863)⟩, true⟩

def words09 : List Nat := [360581630369977492, 360581631847574992, 360581634062607086, 360581635540432954, 360581636254710721, 360581636968985511, 360581638121553018, 360581639645739299, 360581641138425567, 360581642631137110]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 36790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 36700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 36700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk367B
