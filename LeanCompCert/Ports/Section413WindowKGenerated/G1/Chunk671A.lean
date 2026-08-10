import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk671A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496309788332956, 362496376386934370⟩, ⟨(-732249059662088768), (-729230875085691342)⟩, true⟩

def state01 : KState := ⟨⟨362495206138194247, 362495272757476254⟩, ⟨(-658192867971364080), (-655173295621315014)⟩, true⟩

def words00 : List Nat := [371285508890614842, 371285508892944698, 371285509071113409, 371285509273093491, 371285509541848202, 371285509652510932, 371285509762928849, 371285509874101059, 371285510077235977, 371285510225318764]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 67100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 67100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484551555142357, 362484618195068775⟩, ⟨56931687256889717, 59952645158819657⟩, true⟩

def words01 : List Nat := [371285510486712332, 371285510749039600, 371285511009361076, 371285511029947632, 371285511105423962, 371285511182059666, 371285511429126289, 371285511431418281, 371285511421582439, 371285511410878651]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 67110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 67100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495865779500770, 362495932439948155⟩, ⟨(-702514650065472220), (-699492314691642868)⟩, true⟩

def words02 : List Nat := [371285511607446225, 371285511748878810, 371285511944454982, 371285512140908979, 371285512301481055, 371285512303772021, 371285512194254666, 371285512222731694, 371285512471577625, 371285512629209575]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 67120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 67100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487674084195903, 362487740765501646⟩, ⟨(-152561037615859164), (-149537301913871218)⟩, true⟩

def words03 : List Nat := [371285512784978256, 371285512941490701, 371285513146248218, 371285513255880310, 371285513407002503, 371285513559029055, 371285513667911426, 371285513670202828, 371285513516581965, 371285513552592785]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 67130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 67100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488938987632025, 362489005689347429⟩, ⟨(-237476483033535450), (-234451376923030736)⟩, true⟩

def words04 : List Nat := [371285513808829155, 371285513811121084, 371285513800127822, 371285513790330320, 371285513809054128, 371285513811586538, 371285513920393822, 371285514075988410, 371285514229379502, 371285514283755212]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 67140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 67100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk671A
