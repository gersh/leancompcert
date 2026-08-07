import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk932

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360601742290393243, 360601799542135133⟩, ⟨(-1845034890454848503), (-1841431775204178267)⟩, true⟩

def state01 : KState := ⟨⟨360582041749433881, 360582099014014532⟩, ⟨(-8970853027473765), (-5366541140906275)⟩, true⟩

def words00 : List Nat := [360582042051447681, 360582042085758507, 360582042097287167, 360582042109219129, 360582042110367769, 360582042042590695, 360582041912468946, 360582041724648629, 360582041536573648, 360582041439896232]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360566939960049087, 360566997237349530⟩, ⟨1398799427210368481, 1402404924772241429⟩, true⟩

def words01 : List Nat := [360582041480626259, 360582041521634596, 360582041522847821, 360582041524312400, 360582041525441536, 360582041500645175, 360582041496604648, 360582041497953959, 360582041432143693, 360582041272157214]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590898570184327, 360590955860220279⟩, ⟨(-834767573549767684), (-831160888721030398)⟩, true⟩

def words02 : List Nat := [360582041111867753, 360582041037536246, 360582041020965442, 360582041000224075, 360582040979387692, 360582040848768435, 360582040720752846, 360582040673877639, 360582040693225066, 360582040790246547]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578629789920322, 360578687092841087⟩, ⟨309089115528722308, 312697001668828850⟩, true⟩

def words03 : List Nat := [360582040829202305, 360582040868291984, 360582040869404290, 360582040943764166, 360582040966483107, 360582040989436483, 360582040990638777, 360582040955771551, 360582040805924362, 360582040771537664]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360568364676762910, 360568421992385810⟩, ⟨1266294597341182524, 1269903667893030510⟩, true⟩

def words04 : List Nat := [360582040815657471, 360582040842980855, 360582040844183190, 360582040813710743, 360582040783021859, 360582040685735598, 360582040645451187, 360582040542509961, 360582040439439279, 360582040262282787]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360609094115968370, 360609151444324514⟩, ⟨(-2531948391501488758), (-2528338133511126264)⟩, true⟩

def words05 : List Nat := [360582040117334937, 360582040087731560, 360582040141575752, 360582040229636768, 360582040230881580, 360582040221252086, 360582040315318677, 360582040512772755, 360582040804566524, 360582041096660313]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598770677579797, 360598828018807994⟩, ⟨(-1569155621510393171), (-1565544163009073881)⟩, true⟩

def words06 : List Nat := [360582041300109227, 360582041528492799, 360582041871522865, 360582042214943607, 360582042496413047, 360582042663445421, 360582042760231453, 360582042857174518, 360582042939933193, 360582043121433579]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566723587306319, 360566780941246594⟩, ⟨1420088835547216185, 1423701479767135689⟩, true⟩

def words07 : List Nat := [360582043352641506, 360582043584101068, 360582043757648944, 360582043843599884, 360582043844756744, 360582043821492187, 360582043839648726, 360582043840998811, 360582043769412295, 360582043607196071]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592357738379137, 360592415105074867⟩, ⟨(-971140202852060591), (-967526368739902981)⟩, true⟩

def words08 : List Nat := [360582043444667169, 360582043437891385, 360582043594306599, 360582043750977288, 360582043810984378, 360582043812334611, 360582043816563431, 360582043877060950, 360582043934537539, 360582044047108505]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582974367106601, 360583031746654730⟩, ⟨(-95722685995129322), (-92107652820280530)⟩, true⟩

def words09 : List Nat := [360582044069803971, 360582044092638264, 360582044177145959, 360582044331232727, 360582044439213948, 360582044547440540, 360582044587518559, 360582044588868957, 360582044524824890, 360582044536948293]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk932
