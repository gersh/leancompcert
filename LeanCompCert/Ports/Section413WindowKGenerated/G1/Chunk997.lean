import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk997

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

def state06 : KState := ⟨⟨362471752759366520, 362471904552068564⟩, ⟨1332100379837468672, 1342323900072701886⟩, true⟩

def words05 : List Nat := [371285360331486602, 371285360408468117, 371285360474352127, 371285360477859425, 371285360409630050, 371285360369587530, 371285360327754954, 371285360328528316, 371285360215233278, 371285360084346759]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483943750696528, 362484095574780804⟩, ⟨115900215522779502, 126126866611559802⟩, true⟩

def words06 : List Nat := [371285359951847185, 371285359921368654, 371285359864242509, 371285359880902803, 371285359883644880, 371285359884169678, 371285359762158473, 371285359742501975, 371285359747395924, 371285359751052345]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486785610400830, 362486937466434472⟩, ⟨(-167661198183849079), (-157431359341678117)⟩, true⟩

def words07 : List Nat := [371285359741049074, 371285359712480720, 371285359713874302, 371285359717782563, 371285359715357423, 371285359725358249, 371285359733521651, 371285359737091109, 371285359677407008, 371285359697527149]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476851898378733, 362477003785626550⟩, ⟨823562025088018788, 833794978644727148⟩, true⟩

def words08 : List Nat := [371285359756285415, 371285359759793763, 371285359684920649, 371285359611258911, 371285359536265678, 371285359468728939, 371285359349569726, 371285359332302832, 371285359313861635, 371285359281955288]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487917762665841, 362488069681722362⟩, ⟨(-280727108507500885), (-270490980611049815)⟩, true⟩

def words09 : List Nat := [371285359206310221, 371285359216412015, 371285359324947940, 371285359328458355, 371285359320178233, 371285359297359963, 371285359318550674, 371285359322418037, 371285359347275454, 371285359378412666]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk997
