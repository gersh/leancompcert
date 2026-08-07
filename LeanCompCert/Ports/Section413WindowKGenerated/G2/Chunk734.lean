import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk734

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360593561677250262, 360593596531732506⟩, ⟨(-820374314855309857), (-818646329648089395)⟩, true⟩

def state01 : KState := ⟨⟨360584883506380701, 360584918370807191⟩, ⟨(-183418279801491532), (-181689564636999320)⟩, true⟩

def words00 : List Nat := [360582443503323377, 360582443563276060, 360582443651600813, 360582443740234230, 360582443755236273, 360582443756282478, 360582443730851657, 360582443613034563, 360582443495034419, 360582443407046488]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 73400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 73400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574554565787473, 360574589440040115⟩, ⟨574926083198537357, 576655519750020599⟩, true⟩

def words01 : List Nat := [360582443496230006, 360582443585606789, 360582443586546170, 360582443615930317, 360582443616803749, 360582443603505832, 360582443760613621, 360582443761657094, 360582443748059101, 360582443642161472]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 73410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 73400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591285459073217, 360591320343191344⟩, ⟨(-653570503353324477), (-651840342429784401)⟩, true⟩

def words02 : List Nat := [360582443614246137, 360582443785956178, 360582443876711120, 360582443967651254, 360582443968621555, 360582443875720157, 360582443597393192, 360582443457683379, 360582443317670358, 360582443433678608]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 73420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 73400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360576502418518630, 360576537312586478⟩, ⟨432072648024586174, 433803539604602356⟩, true⟩

def words03 : List Nat := [360582443443620479, 360582443453666816, 360582443648639401, 360582443937467894, 360582444138130583, 360582444338963050, 360582444387884853, 360582444388928766, 360582444302755662, 360582444223528807]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 73430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 73400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360571179410757051, 360571214314650065⟩, ⟨822994774324212309, 824726387514202179⟩, true⟩

def words04 : List Nat := [360582444231516520, 360582444232560352, 360582444135914796, 360582443947043182, 360582443757988387, 360582443481388672, 360582443297990410, 360582443136692147, 360582442975293346, 360582442720198251]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 73440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 73400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk734
