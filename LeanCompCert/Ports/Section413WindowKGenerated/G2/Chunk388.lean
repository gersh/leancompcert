import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk388

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

def state06 : KState := ⟨⟨360542477453367960, 360542486733228483⟩, ⟨1549756354304605853, 1550000100679678155⟩, true⟩

def words05 : List Nat := [360582371173684682, 360582372788872032, 360582374061771307, 360582374676163707, 360582374970729039, 360582375265417232, 360582375265851462, 360582375229544500, 360582374534755403, 360582373508850709]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 38850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 38800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360604902816056041, 360604912100873818⟩, ⟨(-876429447879354122), (-876185508840991150)⟩, true⟩

def words06 : List Nat := [360582372482879404, 360582372230790566, 360582372442587292, 360582372654479879, 360582372654964121, 360582372299937419, 360582371286604725, 360582370933891226, 360582370667117615, 360582371247568244]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 38860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 38800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360619520224002246, 360619529513834186⟩, ⟨(-1444699856368095775), (-1444455722404784103)⟩, true⟩

def words07 : List Nat := [360582371315044423, 360582371382562310, 360582372110185816, 360582373356262608, 360582374408316710, 360582375460401895, 360582376181510217, 360582376918281573, 360582377874278416, 360582378830405139]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 38870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 38800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586629032545922, 360586638327321490⟩, ⟨(-165774301526557518), (-165529975329526012)⟩, true⟩

def words08 : List Nat := [360582380227120192, 360582380966216329, 360582381281069011, 360582381595960797, 360582381596411252, 360582381265439538, 360582381642010478, 360582382020420782, 360582382020893765, 360582382073295378]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 38880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 38800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592605701202254, 360592615000949105⟩, ⟨(-398237998805843686), (-397993479251045914)⟩, true⟩

def words09 : List Nat := [360582382842668146, 360582383612165242, 360582384313514512, 360582384357724609, 360582384358209284, 360582383836685035, 360582383315079640, 360582383542112897, 360582383805564916, 360582384069115707]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 38890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 38800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 38800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk388
