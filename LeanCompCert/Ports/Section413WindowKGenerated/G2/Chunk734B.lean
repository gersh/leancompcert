import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk734A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk734B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk734A

def state06 : KState := ⟨⟨360590675394030461, 360590710307792663⟩, ⟨(-609152708068159323), (-607420369938685287)⟩, true⟩

def words05 : List Nat := [360582442568188022, 360582442409690397, 360582442276288201, 360582442277334370, 360582442224046362, 360582442004335210, 360582441784433352, 360582441543052189, 360582441584006482, 360582441697646617]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 73450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 73400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360567226767474194, 360567261691172123⟩, ⟨1113416196893164509, 1115149264950842645⟩, true⟩

def words06 : List Nat := [360582441702930386, 360582441703976021, 360582441623828584, 360582441598615464, 360582441573141789, 360582441420651175, 360582441126169080, 360582440736353871, 360582440346355198, 360582439985237059]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 73460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 73400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360553962942849361, 360553997876400962⟩, ⟨2088063996138190148, 2089797788194261684⟩, true⟩

def words07 : List Nat := [360582439779492578, 360582439758927766, 360582439738233229, 360582439604182040, 360582439408288193, 360582439166190244, 360582438923776316, 360582438866502867, 360582438624209412, 360582438238243563]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 73470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 73400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595558703881351, 360595593647281525⟩, ⟨(-968557205573701302), (-966822689795692434)⟩, true⟩

def words08 : List Nat := [360582437852044374, 360582437620431159, 360582437585806362, 360582437661569174, 360582437662543177, 360582437559174188, 360582437594956857, 360582437673351862, 360582437806088754, 360582437986182946]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 73480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 73400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575848402523405, 360575883355886511⟩, ⟨480022762626528099, 481758010628375523⟩, true⟩

def words09 : List Nat := [360582437997964282, 360582438009852473, 360582438017457791, 360582438120230539, 360582438175851996, 360582438231642161, 360582438232573135, 360582438196110315, 360582437974607733, 360582437886643360]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 73490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 73400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 73400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk734B
