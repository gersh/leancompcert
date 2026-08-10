import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk230A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk230B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk230A

def state06 : KState := ⟨⟨360658013141367138, 360658016267026075⟩, ⟨(-1789162398338665420), (-1789113633454379642)⟩, true⟩

def words05 : List Nat := [360580429319371784, 360580429052591415, 360580430396812140, 360580430397111243, 360580430139070389, 360580428220448070, 360580426301933246, 360580427748609063, 360580431113487804, 360580434478142056]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 23050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 23000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360613130325691052, 360613133454198731⟩, ⟨(-754034050372585448), (-753985219782025668)⟩, true⟩

def words06 : List Nat := [360580436898405283, 360580438793322397, 360580442564788863, 360580446336015731, 360580448832416840, 360580450570978598, 360580450857068030, 360580451143161102, 360580451143404447, 360580452373197387]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 23060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 23000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360565582727190098, 360565585858520950⟩, ⟨343329342800179734, 343378238535646994⟩, true⟩

def words07 : List Nat := [360580455665819252, 360580458958217868, 360580461307599720, 360580462387619663, 360580462387871904, 360580462300326942, 360580463360101914, 360580464242554924, 360580464242826408, 360580463598492166]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 23070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 23000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360703150315026861, 360703153449184823⟩, ⟨(-2832323608833988836), (-2832274647834984284)⟩, true⟩

def words08 : List Nat := [360580464183767835, 360580466353468353, 360580469560550249, 360580472767411552, 360580474423889855, 360580477109550787, 360580481668100069, 360580486226343469, 360580491056157940, 360580496368597799]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 23080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 23000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360655779139400865, 360655782276415395⟩, ⟨(-1738371792269674953), (-1738322765298676097)⟩, true⟩

def words09 : List Nat := [360580500557635094, 360580504746342571, 360580508864256809, 360580513935684910, 360580518125422197, 360580522314845241, 360580525563265477, 360580526950254899, 360580530208303814, 360580533466177801]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 23090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 23000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 23000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk230B
