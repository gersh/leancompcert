import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk388A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360608657690843404, 360608666940907128⟩, ⟨(-1023200129963025379), (-1022957540596147233)⟩, true⟩

def state01 : KState := ⟨⟨360644940538288363, 360644949793309877⟩, ⟨(-2431229147044980012), (-2430986365291785530)⟩, true⟩

def words00 : List Nat := [360582303178346615, 360582304065501290, 360582305614937510, 360582307164394382, 360582308166901343, 360582308509431677, 360582309355555978, 360582310201809724, 360582311648853206, 360582313263323745]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 38800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 38800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360616637875148479, 360616647135162715⟩, ⟨(-1332650482683922320), (-1332407507137877260)⟩, true⟩

def words01 : List Nat := [360582314414764647, 360582315566202759, 360582317097412432, 360582318960074636, 360582320369433835, 360582321778798486, 360582322755706350, 360582323542413321, 360582324427013379, 360582325311738850]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 38810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 38800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360655916290802919, 360655925555765662⟩, ⟨(-2857577377061462107), (-2857334209389823311)⟩, true⟩

def words02 : List Nat := [360582326858077230, 360582328631325502, 360582330072591397, 360582331513841195, 360582332781804062, 360582334388896789, 360582336380129868, 360582338371362112, 360582339817145451, 360582341712717844]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 38820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 38800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360686432879201459, 360686442149112576⟩, ⟨(-4042855583133947244), (-4042612223291886996)⟩, true⟩

def words03 : List Nat := [360582343508637325, 360582345304615690, 360582347761776754, 360582349559892988, 360582350793280996, 360582352026652307, 360582353715069796, 360582355734403654, 360582358414704896, 360582361094986990]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 38830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 38800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360619419047284134, 360619428322203271⟩, ⟨(-1440013582303934438), (-1439770027926988804)⟩, true⟩

def words04 : List Nat := [360582363262455263, 360582364771101728, 360582366099992384, 360582367428968863, 360582368361627836, 360582368635626289, 360582368636094658, 360582368476366941, 360582368604014908, 360582369558518244]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 38840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 38800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk388A
