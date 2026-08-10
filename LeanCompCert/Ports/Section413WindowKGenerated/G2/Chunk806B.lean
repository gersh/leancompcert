import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk806A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk806B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk806A

def state06 : KState := ⟨⟨360597693351784091, 360597735755415536⟩, ⟨(-1261210260891578819), (-1258900304290819987)⟩, true⟩

def words05 : List Nat := [360582128639571605, 360582128499483731, 360582128359045692, 360582128321952644, 360582128292394602, 360582128140457068, 360582127988701018, 360582128067792640, 360582128262225472, 360582128456915756]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580006186096403, 360580048600733622⟩, ⟨165382713169689894, 167693557550479776⟩, true⟩

def words06 : List Nat := [360582128522412552, 360582128523567635, 360582128497171990, 360582128494730456, 360582128491990440, 360582128365234013, 360582128133692176, 360582127824873914, 360582127515821520, 360582127360589213]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360588563142232713, 360588605567738581⟩, ⟨(-524914057414794681), (-522602336206342457)⟩, true⟩

def words07 : List Nat := [360582127463411436, 360582127592219966, 360582127644172871, 360582127737991115, 360582127738975247, 360582127727517306, 360582127856367761, 360582128014526320, 360582128095841889, 360582128177321924]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360614461638692689, 360614504075107091⟩, ⟨(-2614455286872277900), (-2612142685510224038)⟩, true⟩

def words08 : List Nat := [360582128411927139, 360582128781294532, 360582129303673290, 360582129826261988, 360582130193144020, 360582130406806008, 360582130773615262, 360582131140755005, 360582131503760588, 360582131906147601]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592532166413340, 360592574613825224⟩, ⟨(-844835246832319863), (-842521758029191221)⟩, true⟩

def words09 : List Nat := [360582132210850826, 360582132515667507, 360582132828598603, 360582133219141392, 360582133571133233, 360582133923332810, 360582134175880855, 360582134311714535, 360582134442022733, 360582134572710131]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk806B
