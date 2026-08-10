import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk236A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk236B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk236A

def state06 : KState := ⟨⟨360636854173375683, 360636857471370676⟩, ⟨(-1306809081195309979), (-1306756290304532961)⟩, true⟩

def words05 : List Nat := [360581618149104767, 360581621162890365, 360581623689222217, 360581624442633929, 360581624442918266, 360581623741163299, 360581623335561037, 360581624523913144, 360581626858606443, 360581629193178523]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 23650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 23600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595632073267842, 360595635374194697⟩, ⟨(-331699960256290122), (-331647099983197558)⟩, true⟩

def words06 : List Nat := [360581630145152836, 360581630145460637, 360581630287189887, 360581631248951368, 360581631754884755, 360581631755192592, 360581630489764199, 360581627762713678, 360581625035834911, 360581624681786975]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 23660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 23600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360595660023609650, 360595663327435564⟩, ⟨(-332102754647338921), (-332049825738768125)⟩, true⟩

def words07 : List Nat := [360581627054331940, 360581629426737131, 360581630648262546, 360581632615661459, 360581634104638909, 360581635593571439, 360581638862069763, 360581640360255772, 360581640952719086, 360581641545173888]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 23670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 23600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360666934055759460, 360666937362497671⟩, ⟨(-2020590942266915818), (-2020537944380700118)⟩, true⟩

def words08 : List Nat := [360581641545428122, 360581642114724072, 360581643107061952, 360581644099373321, 360581644099657376, 360581643572787149, 360581643312304811, 360581644071520710, 360581646608933197, 360581650209385490]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 23680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 23600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360629458519196004, 360629461828868494⟩, ⟨(-1132688938515463145), (-1132635871101628145)⟩, true⟩

def words09 : List Nat := [360581652723048859, 360581655236533503, 360581657540494790, 360581661226460706, 360581663707221557, 360581666187818769, 360581667761781253, 360581669268618099, 360581671285432512, 360581673302177569]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 23690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 23600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 23600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk236B
