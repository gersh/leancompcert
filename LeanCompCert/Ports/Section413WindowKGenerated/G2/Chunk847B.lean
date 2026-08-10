import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk847A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk847B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk847A

def state06 : KState := ⟨⟨360572109394946549, 360572156399617295⟩, ⟨869784140381551035, 872474732181198717⟩, true⟩

def words05 : List Nat := [360582449345539735, 360582449627465442, 360582449824275958, 360582449938973792, 360582449940001072, 360582449932167217, 360582450026524938, 360582450027742375, 360582449992331256, 360582449872153648]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 84750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 84700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360597801467683982, 360597848483859364⟩, ⟨(-1308010754243065113), (-1305319187253879463)⟩, true⟩

def words06 : List Nat := [360582449769335212, 360582449886045935, 360582449998733730, 360582450111635044, 360582450112757961, 360582450107046849, 360582450080011163, 360582450058551375, 360582450120098587, 360582450303028020]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 84760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 84700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593287386991116, 360593334414772563⟩, ⟨(-925338536482717379), (-922645985591119005)⟩, true⟩

def words07 : List Nat := [360582450416147977, 360582450529387907, 360582450683800458, 360582450916966426, 360582451113506484, 360582451310239390, 360582451375490443, 360582451458046549, 360582451587400675, 360582451717168252]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 84770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 84700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596891367869771, 360596938407114745⟩, ⟨(-1230948206742628895), (-1228254683915489645)⟩, true⟩

def words08 : List Nat := [360582451954672552, 360582452053404193, 360582452069372673, 360582452085494659, 360582452086514676, 360582452084796888, 360582452267001334, 360582452449444089, 360582452562193790, 360582452734296693]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 84780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 84700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360596713919390203, 360596760970152425⟩, ⟨(-1215913196808236111), (-1213218697376486827)⟩, true⟩

def words09 : List Nat := [360582452902513043, 360582453071065993, 360582453378225512, 360582453546633677, 360582453596490494, 360582453646445719, 360582453757419091, 360582453974917443, 360582454144628095, 360582454314601471]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 84790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 84700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 84700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk847B
