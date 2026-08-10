import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk861A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk861B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk861A

def state06 : KState := ⟨⟨360551510483224201, 360551559115187239⟩, ⟨2642152050134284947, 2644981713554488755⟩, true⟩

def words05 : List Nat := [360582260833225574, 360582260394448075, 360582259955434793, 360582259617047194, 360582259351970181, 360582259053274271, 360582258754436420, 360582258387290837, 360582257957928898, 360582257603041864]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 86150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 86100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360556381874706842, 360556430518352886⟩, ⟨2222365543492681849, 2225196213580153405⟩, true⟩

def words06 : List Nat := [360582257247751092, 360582257027234760, 360582256712779483, 360582256270998324, 360582255829021584, 360582255323097670, 360582254884566906, 360582254561125500, 360582254237556380, 360582253846814998]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 86160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 86100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360568869157630799, 360568917812966881⟩, ⟨1146258937515905426, 1149090614991877992⟩, true⟩

def words07 : List Nat := [360582253548141167, 360582253384334363, 360582253220170135, 360582253046044966, 360582252851566970, 360582252541556043, 360582252231337152, 360582251865827507, 360582251577623480, 360582251424187488]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 86170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 86100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360560658897815131, 360560707564960056⟩, ⟨1853767442724545285, 1856600137941724211⟩, true⟩

def words08 : List Nat := [360582251270576714, 360582251031314356, 360582250712797723, 360582250529165727, 360582250345175136, 360582250073667799, 360582249667384552, 360582249193881786, 360582248720151435, 360582248348553765]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 86180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 86100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360549673375193216, 360549722054016483⟩, ⟨2800635503441011803, 2803469205272654759⟩, true⟩

def words09 : List Nat := [360582248099654203, 360582247847521195, 360582247595269359, 360582247258379926, 360582246827987299, 360582246364104652, 360582245899859438, 360582245570310448, 360582245274640044, 360582244898625215]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 86190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 86100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 86100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk861B
