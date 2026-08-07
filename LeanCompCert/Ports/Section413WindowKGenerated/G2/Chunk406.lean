import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk406

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360565721218459618, 360565731384025020⟩, ⟨682131177798780123, 682410119248828061⟩, true⟩

def state01 : KState := ⟨⟨360593982320204926, 360593992490964009⟩, ⟨(-465464151911024437), (-465184999571249281)⟩, true⟩

def words00 : List Nat := [360582539101506223, 360582538857353472, 360582539198868561, 360582539540471286, 360582539540979143, 360582539367025878, 360582538773932830, 360582538165614926, 360582537557159383, 360582537835831872]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598153829556219, 360598164005560583⟩, ⟨(-634920063337403356), (-634640697960538734)⟩, true⟩

def words01 : List Nat := [360582537836322680, 360582537815411316, 360582537977822742, 360582538636315368, 360582539140734830, 360582539645219332, 360582539844822333, 360582539845374127, 360582540157124491, 360582540542377488]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360596966999929157, 360596977181131162⟩, ⟨(-586863193000647938), (-586583616470110464)⟩, true⟩

def words02 : List Nat := [360582540899944505, 360582540997423172, 360582540997917371, 360582540633461565, 360582540268936564, 360582539578064523, 360582539656379541, 360582539998023305, 360582539998514719, 360582540332014229]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360667745721456460, 360667755907857992⟩, ⟨(-3463060474927127656), (-3462780687113912906)⟩, true⟩

def words03 : List Nat := [360582541039000960, 360582541746114146, 360582542914067518, 360582543995296184, 360582544495275024, 360582544995258144, 360582546099124219, 360582547592485653, 360582549689592718, 360582551786721359]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360630257274785085, 360630267466442922⟩, ⟨(-1939420454869130245), (-1939140453413455663)⟩, true⟩

def words04 : List Nat := [360582553452123891, 360582555131901013, 360582557231811419, 360582559331785582, 360582561033695373, 360582562133144460, 360582562805114563, 360582563477110541, 360582564133626260, 360582565307740469]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360574366348453707, 360574376545304866⟩, ⟨332813516471505902, 333093729061584004⟩, true⟩

def words05 : List Nat := [360582566411757030, 360582567515822548, 360582568315771372, 360582568513450194, 360582568513912008, 360582568456775259, 360582568816061688, 360582568918108325, 360582568918599786, 360582568717687099]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 40650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 40600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589051031007750, 360589061233074880⟩, ⟨(-264383574601797216), (-264103149904752654)⟩, true⟩

def words06 : List Nat := [360582568746581110, 360582569298736289, 360582569642940478, 360582569987230202, 360582569987738904, 360582569818586652, 360582569047407211, 360582568368232081, 360582567688928916, 360582567585269202]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 40660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 40600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593199236246957, 360593209443572156⟩, ⟨(-433120575477977971), (-432839936909252407)⟩, true⟩

def words07 : List Nat := [360582567585765406, 360582567442495381, 360582567602882328, 360582568209719364, 360582568664884985, 360582569120117675, 360582569120620225, 360582569067074906, 360582569326493960, 360582569588678981]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 40670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 40600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360556651743091392, 360556661955614370⟩, ⟨1053743469608960029, 1054024319649408993⟩, true⟩

def words08 : List Nat := [360582570055148690, 360582570055700710, 360582569920717301, 360582569424434847, 360582568928077438, 360582568169467051, 360582567712909577, 360582567207740728, 360582566702544867, 360582565723607720]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 40680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 40600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360606617850037748, 360606628067780665⟩, ⟨(-979819488977761651), (-979538426512816697)⟩, true⟩

def words09 : List Nat := [360582565087465056, 360582564436410679, 360582563785226712, 360582563736460995, 360582563086474199, 360582561924544303, 360582560762565934, 360582560203035895, 360582560783997666, 360582561375893173]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 40690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 40600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 40600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk406
