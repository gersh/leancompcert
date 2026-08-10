import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk997A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362477315490552385, 362477467093651468⟩, ⟨776541852082513100, 786746463206393272⟩, true⟩

def state01 : KState := ⟨⟨362485727286025491, 362485878920548458⟩, ⟨(-62161785347919944), (-51954041105664310)⟩, true⟩

def words00 : List Nat := [371285358154968184, 371285358121263038, 371285358061103886, 371285358079047526, 371285358081771445, 371285358066282603, 371285357915585726, 371285357867360224, 371285357865440290, 371285357874313784]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 99700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 99700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486690273227496, 362486841939724222⟩, ⟨(-158178093782173830), (-147967161279724836)⟩, true⟩

def words01 : List Nat := [371285357881733404, 371285357890371105, 371285357998126483, 371285358057140348, 371285358096777446, 371285358137663947, 371285358173937728, 371285358177444268, 371285358108979700, 371285358128277489]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 99710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 99700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489807410537947, 362489959108309500⟩, ⟨(-468990352497099895), (-458776301106334147)⟩, true⟩

def words02 : List Nat := [371285358246132221, 371285358301124162, 371285358354474693, 371285358408965145, 371285358493043348, 371285358542970415, 371285358674917421, 371285358808339971, 371285358921172637, 371285358970928883]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 99720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 99700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498425801245652, 362498577530674269⟩, ⟨(-1328539708155340459), (-1318322499443808835)⟩, true⟩

def words03 : List Nat := [371285359072579794, 371285359176003041, 371285359378218925, 371285359465874446, 371285359535896972, 371285359607127398, 371285359728404377, 371285359801130495, 371285359936036511, 371285360072463064]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 99730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 99700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485319705663585, 362485471466779101⟩, ⟨(-21313759529745138), (-11093390207466966)⟩, true⟩

def words04 : List Nat := [371285360207502529, 371285360211009548, 371285360251794181, 371285360295980311, 371285360368709110, 371285360372217111, 371285360325708595, 371285360280317955, 371285360250761998, 371285360255962092]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 99740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 99700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk997A
