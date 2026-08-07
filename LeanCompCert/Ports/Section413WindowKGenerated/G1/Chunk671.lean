import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk671

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

def state06 : KState := ⟨⟨362508133771320427, 362508200493805148⟩, ⟨(-1526547374343897627), (-1523520873472451807)⟩, true⟩

def words05 : List Nat := [371285514409390774, 371285514536213410, 371285514883255366, 371285514935669547, 371285514937455978, 371285514908696925, 371285515069220824, 371285515207358797, 371285515546693092, 371285515887062062]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 67150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 67100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362497963498600634, 362498030241739452⟩, ⟨(-843528274871842902), (-840500386764939498)⟩, true⟩

def words06 : List Nat := [371285516209354320, 371285516236927692, 371285516447984482, 371285516660199729, 371285516867903363, 371285516916581575, 371285516939317876, 371285516962838875, 371285517206718162, 371285517395618881]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 67160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 67100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476377117327442, 362476443881105346⟩, ⟨606612556022900796, 609641830564191396⟩, true⟩

def words07 : List Nat := [371285517730198342, 371285518065715214, 371285518400808706, 371285518441299244, 371285518547513897, 371285518654905515, 371285518856542983, 371285518858835515, 371285518765503970, 371285518632974418]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 67170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 67100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362498831971352174, 362498898755655377⟩, ⟨(-901991297111334694), (-898960643575554298)⟩, true⟩

def words08 : List Nat := [371285518585609764, 371285518588136022, 371285518682256728, 371285518802123636, 371285518886415945, 371285518888748634, 371285518907690894, 371285519029723522, 371285519371773172, 371285519573271196]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 67180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 67100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481330320194613, 362481397125445341⟩, ⟨274074365175948431, 277106426275088519⟩, true⟩

def words09 : List Nat := [371285519774486986, 371285519976492762, 371285520223900857, 371285520362516949, 371285520543517965, 371285520725371094, 371285520904819192, 371285520907112339, 371285520791414455, 371285520732979197]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 67190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 67100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 67100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk671
