import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk614A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360595885977994633, 360595910023232507⟩, ⟨(-821846968981814368), (-820849601071992618)⟩, true⟩

def state01 : KState := ⟨⟨360602603229013805, 360602627282443128⟩, ⟨(-1234444444128175416), (-1233446573223342140)⟩, true⟩

def words00 : List Nat := [360582541409528312, 360582541423329468, 360582541701998796, 360582541980930991, 360582542192012092, 360582542192872678, 360582542139848423, 360582541954006142, 360582541846299460, 360582542174348107]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 61400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 61400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360575346005201631, 360575370066744592⟩, ⟨439492447852262196, 440490817056386956⟩, true⟩

def words01 : List Nat := [360582542440814624, 360582542707428890, 360582542772196659, 360582542773057391, 360582542573681285, 360582542265290728, 360582541956648807, 360582541963310722, 360582541964077593, 360582541848201062]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 61410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 61400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360588819113852960, 360588843183520794⟩, ⟨(-388064777510861714), (-387065909237879772)⟩, true⟩

def words02 : List Nat := [360582541732134480, 360582541846277808, 360582542198740317, 360582542551362182, 360582542661581402, 360582542662442331, 360582542508503627, 360582542364612775, 360582542256221709, 360582542359682051]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 61420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 61400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577236519751667, 360577260597628259⟩, ⟨323524427683600193, 324523800263087401⟩, true⟩

def words03 : List Nat := [360582542360448917, 360582542330796285, 360582542392820695, 360582542620506693, 360582542677692593, 360582542735012422, 360582542735779384, 360582542660062519, 360582542645511971, 360582542560523167]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 61430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 61400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593200148998743, 360593224234980732⟩, ⟨(-657365738008263008), (-656365867393001326)⟩, true⟩

def words04 : List Nat := [360582542654018380, 360582542677843589, 360582542678617776, 360582542569764315, 360582542460773792, 360582542355872083, 360582542592963247, 360582542830211537, 360582542934374768, 360582543109085418]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 61440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 61400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk614A
