import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk734A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk734A
