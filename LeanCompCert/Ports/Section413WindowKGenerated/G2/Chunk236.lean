import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk236

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360675433953607320, 360675437234152806⟩, ⟨(-2217528450398880469), (-2217476071839044873)⟩, true⟩

def state01 : KState := ⟨⟨360711520789153841, 360711524072621214⟩, ⟨(-3069797130096561584), (-3069744682565557096)⟩, true⟩

def words00 : List Nat := [360581483444561217, 360581484745466356, 360581487836592535, 360581490927552013, 360581493558498645, 360581496912924038, 360581499091554268, 360581501270032106, 360581505237770709, 360581510744826307]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 23600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 23600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598403072121326, 360598406358483276⟩, ⟨(-398529630979020590), (-398477115092143528)⟩, true⟩

def words01 : List Nat := [360581516193471606, 360581521641709702, 360581525853212829, 360581528286889395, 360581530261688579, 360581532236404675, 360581533702488829, 360581535316988548, 360581536031531635, 360581536746058225]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 23610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 23600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360685465961350116, 360685469250611963⟩, ⟨(-2455613644381970336), (-2455561059985613924)⟩, true⟩

def words02 : List Nat := [360581537063892956, 360581538439946156, 360581541603328248, 360581544766501096, 360581546234873066, 360581546235180316, 360581547406010471, 360581548885070351, 360581552150843998, 360581556548653282]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 23620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 23600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360645013857380319, 360645017149572278⟩, ⟨(-1499289996153346765), (-1499237342503929189)⟩, true⟩

def words03 : List Nat := [360581560047191554, 360581563545472448, 360581568829757292, 360581575342629110, 360581580960450565, 360581586577847092, 360581591296586289, 360581594950798934, 360581597633887804, 360581600316845070]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 23630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 23600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360624787937128700, 360624791232216708⟩, ⟨(-1021210593676128716), (-1021157871549718226)⟩, true⟩

def words04 : List Nat := [360581604173933155, 360581606256693599, 360581607089254454, 360581607921776102, 360581608296329964, 360581610084578666, 360581611458358302, 360581612832078582, 360581613309208869, 360581615135157399]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 23640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 23600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk236
