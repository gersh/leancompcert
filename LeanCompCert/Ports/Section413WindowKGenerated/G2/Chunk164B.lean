import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk164A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk164B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk164A

def state06 : KState := ⟨⟨360734903307573384, 360734904852530088⟩, ⟨(-2502669742640556780), (-2502652526695266680)⟩, true⟩

def words05 : List Nat := [360582810119871386, 360582815337695267, 360582824239687364, 360582831662546886, 360582835983283921, 360582840303514093, 360582844503329181, 360582851110930231, 360582860348871054, 360582869585736135]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 16450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 16400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360626053761707557, 360626055308640998⟩, ⟨(-710980417759144774), (-710963169267315812)⟩, true⟩

def words06 : List Nat := [360582876460169289, 360582879679777833, 360582885268036894, 360582890855681408, 360582894479469877, 360582894479677446, 360582894449906897, 360582891620041441, 360582888790479905, 360582890766763316]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 16460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 16400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360541997296336221, 360541998845227871⟩, ⟨673490084097996830, 673507364851408268⟩, true⟩

def words07 : List Nat := [360582891787543070, 360582892808235046, 360582892808420947, 360582891020822684, 360582885582928903, 360582879201475698, 360582872820736742, 360582870115001137, 360582869490370818, 360582867010570797]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 16470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 16400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360675738161638860, 360675739712491021⟩, ⟨(-1531086462975232898), (-1531069149902910482)⟩, true⟩

def words08 : List Nat := [360582865724460002, 360582869517071839, 360582875645887113, 360582881773999353, 360582884305791341, 360582884305999213, 360582885743998668, 360582888297874192, 360582891370862254, 360582897001321116]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 16480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 16400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360628977882019234, 360628979434854278⟩, ⟨(-759576783170578837), (-759559437390803261)⟩, true⟩

def words09 : List Nat := [360582900221152093, 360582903440619172, 360582910327281614, 360582919047869409, 360582926793702113, 360582934538629624, 360582939831105340, 360582942739045336, 360582945529319333, 360582948319322444]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 16490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 16400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 16400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk164B
