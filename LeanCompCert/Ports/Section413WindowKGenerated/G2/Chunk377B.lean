import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk377A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk377B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk377A

def state06 : KState := ⟨⟨360611786987776736, 360611795729181272⟩, ⟨(-1139122275918195980), (-1138899159302695354)⟩, true⟩

def words05 : List Nat := [360581633467634316, 360581633702119230, 360581634233651250, 360581634340450626, 360581634340924286, 360581633847140859, 360581633353287335, 360581633405106207, 360581634204308335, 360581635003583362]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 37750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 37700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576804351509154, 360576813097758582⟩, ⟨181725227071188168, 181948526654287616⟩, true⟩

def words06 : List Nat := [360581635356375905, 360581635356885166, 360581635231187563, 360581635206378397, 360581635181440175, 360581634568716495, 360581633647316326, 360581632374285122, 360581631101223921, 360581630374079850]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 37760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 37700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360574350233489314, 360574358984543676⟩, ⟨274569176567236573, 274792657656322561⟩, true⟩

def words07 : List Nat := [360581630651022278, 360581631055589701, 360581631097056923, 360581631438197789, 360581631596137151, 360581631754202421, 360581632310735102, 360581632671520360, 360581632671982132, 360581632479981906]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 37770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 37700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360634606694738053, 360634615450597983⟩, ⟨(-2002081831077703246), (-2001858168410029918)⟩, true⟩

def words08 : List Nat := [360581632795015780, 360581633656147778, 360581635216689185, 360581636777245520, 360581637630817573, 360581638504290141, 360581639751811206, 360581640999415353, 360581642225185386, 360581643627454642]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 37780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 37700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360604162128583662, 360604170889310198⟩, ⟨(-851496948108353274), (-851273101508275346)⟩, true⟩

def words09 : List Nat := [360581644479332226, 360581645331211889, 360581646161848977, 360581647343055423, 360581648346065767, 360581649349109590, 360581649942780069, 360581649943289849, 360581650436291680, 360581651032652748]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 37790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 37700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 37700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk377B
