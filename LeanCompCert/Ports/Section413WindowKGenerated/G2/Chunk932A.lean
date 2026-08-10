import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk932A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk932A
