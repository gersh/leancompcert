import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk509A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk509B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk509A

def state06 : KState := ⟨⟨360561717070400456, 360561733387180000⟩, ⟨1030886365636081747, 1031448208685568401⟩, true⟩

def words05 : List Nat := [360581981359456449, 360581980766399917, 360581980173165480, 360581979444241675, 360581978447818123, 360581977113965326, 360581975780030057, 360581974830612633, 360581974133087657, 360581973736644003]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 50950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 50900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360543254396279297, 360543270719759213⟩, ⟨1971622706214401899, 1972184890748524851⟩, true⟩

def words06 : List Nat := [360581973340098088, 360581972750979914, 360581971883403704, 360581970939637218, 360581969995720748, 360581968955777451, 360581967789465150, 360581966322363528, 360581964855183627, 360581963772353848]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 50960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 50900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360541497042081787, 360541513372194759⟩, ⟨2061329920045190623, 2061892442700212785⟩, true⟩

def words07 : List Nat := [360581963013804473, 360581962639463678, 360581962265063621, 360581961647588686, 360581961242162114, 360581960735709165, 360581960229062779, 360581959889505155, 360581959289249264, 360581958496610221]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 50970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 50900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581696575953511, 360581712912726359⟩, ⟨11668714267624429, 12231576475708413⟩, true⟩

def words08 : List Nat := [360581957703852552, 360581956901538282, 360581956332568707, 360581955894094514, 360581955455592996, 360581954626976241, 360581953869249210, 360581953383195286, 360581952896940480, 360581952794594877]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 50980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 50900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360566332720851340, 360566349064335798⟩, ⟨795181124205172719, 795744328670476743⟩, true⟩

def words09 : List Nat := [360581952790519139, 360581952540926290, 360581952424626410, 360581952749871296, 360581952778909130, 360581952808056397, 360581952808684378, 360581952618966630, 360581952199446707, 360581951894309729]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 50990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 50900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 50900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk509B
