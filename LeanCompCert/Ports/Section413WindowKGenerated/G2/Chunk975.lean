import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk975

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360591146673130678, 360591209549087800⟩, ⟨(-863429172898046252), (-859289691674600486)⟩, true⟩

def state01 : KState := ⟨⟨360596187700279087, 360596250589580863⟩, ⟨(-1354997541645481542), (-1350856759249932376)⟩, true⟩

def words00 : List Nat := [360582396608551194, 360582396700675337, 360582396711575682, 360582396722618059, 360582396723802782, 360582396744696310, 360582396869864857, 360582396995305356, 360582397067842455, 360582397211405581]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 97500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 97500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602348119055181, 360602411021712264⟩, ⟨(-1955744568063106369), (-1951602483324588431)⟩, true⟩

def words01 : List Nat := [360582397459740463, 360582397708490437, 360582397984203828, 360582398155376544, 360582398225430725, 360582398295572398, 360582398363070212, 360582398483251839, 360582398689611035, 360582398896289796]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 97510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 97500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360601908141920804, 360601971058069880⟩, ⟨(-1912914914526959805), (-1908771513985758419)⟩, true⟩

def words02 : List Nat := [360582399050031363, 360582399099139532, 360582399253067933, 360582399407453509, 360582399515266336, 360582399671550204, 360582399747293957, 360582399823186904, 360582399934604829, 360582400136885993]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 97520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 97500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577659600620293, 360577722530114117⟩, ⟨452171536686342870, 456316238809710824⟩, true⟩

def words03 : List Nat := [360582400336341366, 360582400536044884, 360582400682990853, 360582400725310479, 360582400740826901, 360582400756718731, 360582400788407252, 360582400822613294, 360582400823881742, 360582400777385080]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 97530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 97500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360610782878506200, 360610845821365242⟩, ⟨(-2778859814614403271), (-2774713808781707225)⟩, true⟩

def words04 : List Nat := [360582400763578242, 360582400851403151, 360582400988634655, 360582401126133387, 360582401163441453, 360582401218511249, 360582401378328619, 360582401538569425, 360582401803405296, 360582402096454358]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 97540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 97500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360597416794526159, 360597479750901982⟩, ⟨(-1474862900790362718), (-1470715576330757168)⟩, true⟩

def words05 : List Nat := [360582402336369034, 360582402576452205, 360582402921245656, 360582403331483408, 360582403705724823, 360582404080190938, 360582404396467109, 360582404608168382, 360582404763863498, 360582404920013300]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 97550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 97500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598251638428024, 360598314608146331⟩, ⟨(-1556348964867894699), (-1552200338649690615)⟩, true⟩

def words06 : List Nat := [360582405180680531, 360582405336896187, 360582405419953247, 360582405503159816, 360582405508842507, 360582405604343314, 360582405766715292, 360582405929355133, 360582406024742284, 360582406189265212]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 97560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 97500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360614263935761976, 360614326918867985⟩, ⟨(-3118805463035121521), (-3114655530514963637)⟩, true⟩

def words07 : List Nat := [360582406458438582, 360582406728023221, 360582406972843525, 360582407113213166, 360582407163971694, 360582407214837856, 360582407370407755, 360582407594132548, 360582407922387090, 360582408250986790]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 97570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 97500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360603858656764188, 360603921653350921⟩, ⟨(-2103481032706655112), (-2099329784669453282)⟩, true⟩

def words08 : List Nat := [360582408500267494, 360582408673987657, 360582408952401806, 360582409231229974, 360582409463324045, 360582409626197477, 360582409707930148, 360582409789782796, 360582409921181257, 360582410143225301]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 97580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 97500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585883562989015, 360585946572917562⟩, ⟨(-349156814310445901), (-345004264176668509)⟩, true⟩

def words09 : List Nat := [360582410395790080, 360582410648625539, 360582410848647993, 360582411051036665, 360582411209974852, 360582411369300295, 360582411563943761, 360582411654211588, 360582411691692503, 360582411729379313]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 97590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 97500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 97500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk975
