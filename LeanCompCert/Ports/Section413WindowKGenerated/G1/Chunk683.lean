import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk683

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489854371204813, 362489923468908052⟩, ⟨(-308348516480268595), (-305161137721159431)⟩, true⟩

def state01 : KState := ⟨⟨362497761549349370, 362497830668147484⟩, ⟨(-848493226215161951), (-845304406572110387)⟩, true⟩

def words00 : List Nat := [371285455649059160, 371285455651406108, 371285455642837349, 371285455735894107, 371285455877356115, 371285455892915776, 371285455908033973, 371285455923918722, 371285456131596137, 371285456315457989]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 68300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 68300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362485626504974883, 362485695644819225⟩, ⟨(-19422564326459865), (-16232306907216329)⟩, true⟩

def words01 : List Nat := [371285456712235672, 371285457109972170, 371285457462738613, 371285457530574925, 371285457638718385, 371285457747979323, 371285458038622134, 371285458044562580, 371285458049801914, 371285458055982598]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 68310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 68300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484467547051619, 362484536707786092⟩, ⟨59788743488303370, 62980428225913752⟩, true⟩

def words02 : List Nat := [371285458171218442, 371285458188052966, 371285458340283265, 371285458493443086, 371285458609972029, 371285458612307157, 371285458469773459, 371285458381621936, 371285458415133668, 371285458417550850]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 68320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 68300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488168813748943, 362488237995727720⟩, ⟨(-193118022506225496), (-189924886037186168)⟩, true⟩

def words03 : List Nat := [371285458405807528, 371285458395047931, 371285458524776154, 371285458591841661, 371285458713349966, 371285458835779430, 371285458956603082, 371285458958939334, 371285458875410599, 371285458918950424]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 68330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 68300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468608908586183, 362468678111385344⟩, ⟨1143683759385813457, 1146878318830354493⟩, true⟩

def words04 : List Nat := [371285459012550008, 371285459014885801, 371285458823385043, 371285458593578167, 371285458362862768, 371285458198177443, 371285457925597666, 371285457818616380, 371285457710826905, 371285457603979790]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 68340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 68300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362498371458001503, 362498440681933944⟩, ⟨(-890715977286251943), (-887519973277261571)⟩, true⟩

def words05 : List Nat := [371285457360074199, 371285457331196066, 371285457429347222, 371285457431710414, 371285457431911568, 371285457397634257, 371285457462001448, 371285457464575637, 371285457648666850, 371285457841231245]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 68350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 68300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486634639332303, 362486703884366209⟩, ⟨(-88319935540394977), (-85122488927740429)⟩, true⟩

def words06 : List Nat := [371285458033172751, 371285458090017814, 371285458339900725, 371285458590990311, 371285458854065226, 371285458856401794, 371285458834561189, 371285458812577693, 371285458854802708, 371285458875679372]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 68360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 68300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483201361678473, 362483270627736807⟩, ⟨146504366404177900, 149703250562564536⟩, true⟩

def words07 : List Nat := [371285459109094099, 371285459343431591, 371285459567084635, 371285459572060958, 371285459635532213, 371285459700245368, 371285459950195716, 371285459952532914, 371285459941293523, 371285459911892446]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 68370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 68300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486691601393377, 362486760888390555⟩, ⟨(-92180025090932289), (-88979709026570939)⟩, true⟩

def words08 : List Nat := [371285459951121051, 371285459953722857, 371285460020126521, 371285460099938147, 371285460127733376, 371285460130072660, 371285459917328618, 371285459815956155, 371285459822775671, 371285459844261554]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 68380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 68300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489594837977920, 362489664146313023⟩, ⟨(-290758862605138891), (-287557087136987723)⟩, true⟩

def words09 : List Nat := [371285459846031847, 371285459832902571, 371285459944454588, 371285459965778537, 371285460051235980, 371285460137565212, 371285460178959737, 371285460181313565, 371285460092366220, 371285460156793324]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 68390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 68300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 68300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk683
