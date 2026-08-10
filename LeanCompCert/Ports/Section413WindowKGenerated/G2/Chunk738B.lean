import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk738A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk738B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk738A

def state06 : KState := ⟨⟨360564386822204736, 360564422132458228⟩, ⟨1325764374448472467, 1327525918182912699⟩, true⟩

def words05 : List Nat := [360582397282823485, 360582397159745885, 360582397036477212, 360582396839785313, 360582396785856938, 360582396685856580, 360582396585760931, 360582396343587672, 360582395918045734, 360582395675894228]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 73850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 73800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360562369087486725, 360562404407627534⟩, ⟨1474754673277300486, 1476516947338754788⟩, true⟩

def words06 : List Nat := [360582395433400629, 360582395342446969, 360582395068226711, 360582394683417212, 360582394298437213, 360582393744607573, 360582393307297396, 360582393053187382, 360582392798969719, 360582392453482939]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 73860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 73800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360575702615333013, 360575737945408562⟩, ⟨489661325870143787, 491424333859025399⟩, true⟩

def words07 : List Nat := [360582392183766870, 360582391872632200, 360582391561183976, 360582391361268388, 360582391047547001, 360582390581934187, 360582390116124189, 360582389833593335, 360582389690200992, 360582389601253974]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 73870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 73800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360570713122937134, 360570748463017329⟩, ⟨858259635024809111, 860023382206425093⟩, true⟩

def words08 : List Nat := [360582389512166836, 360582389330562437, 360582389204310254, 360582389233373294, 360582389234267974, 360582389137314084, 360582388857178702, 360582388437244882, 360582388017121779, 360582387702186452]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 73880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 73800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360551990870169913, 360552026220164167⟩, ⟨2241765691388376869, 2243530171168712091⟩, true⟩

def words09 : List Nat := [360582387545518809, 360582387469854107, 360582387394052451, 360582387226990160, 360582386876714850, 360582386480557644, 360582386084102916, 360582385870701311, 360582385630855732, 360582385221127208]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 73890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 73800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 73800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk738B
