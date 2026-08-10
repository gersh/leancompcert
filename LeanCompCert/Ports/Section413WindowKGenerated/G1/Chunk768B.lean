import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk768A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk768B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk768A

def state06 : KState := ⟨⟨362482586779339390, 362482675090060272⟩, ⟨189505762015505575, 194089359486935763⟩, true⟩

def words05 : List Nat := [371285200173298509, 371285200221256481, 371285200338682610, 371285200372551554, 371285200442692953, 371285200513881250, 371285200533391800, 371285200536041761, 371285200351939034, 371285200322424141]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 76850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 76800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471582026196783, 362471670360498226⟩, ⟨1035413517481997207, 1039998927479322207⟩, true⟩

def words06 : List Nat := [371285200403992994, 371285200406642785, 371285200295754890, 371285200185871271, 371285200074937244, 371285200016813667, 371285199885427844, 371285199816644325, 371285199747002552, 371285199681787147]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 76860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 76800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496125209962099, 362496213568240865⟩, ⟨(-851291784351676616), (-846704531096129394)⟩, true⟩

def words07 : List Nat := [371285199507584067, 371285199503857040, 371285199660880171, 371285199739731284, 371285199779709444, 371285199820484780, 371285199998577828, 371285200093791624, 371285200238858158, 371285200385125452]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 76870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 76800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490129189568902, 362490217571775272⟩, ⟨(-390322833076369197), (-385733740143712057)⟩, true⟩

def words08 : List Nat := [371285200496839971, 371285200499502937, 371285200565230747, 371285200684853734, 371285200854900263, 371285200857552167, 371285200832486127, 371285200807448659, 371285200872930135, 371285200941218462]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 76880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 76800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474848975246037, 362474937381279694⟩, ⟨784690806791691285, 789281731923880839⟩, true⟩

def words09 : List Nat := [371285201115669004, 371285201291166189, 371285201457828060, 371285201460478978, 371285201401751134, 371285201346912642, 371285201382352992, 371285201385003968, 371285201253430770, 371285201122917196]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 76890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 76800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 76800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk768B
