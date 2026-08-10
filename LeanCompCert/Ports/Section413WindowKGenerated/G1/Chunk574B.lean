import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk574A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk574B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk574A

def state06 : KState := ⟨⟨362469857902596055, 362469906145695074⟩, ⟨864639873525351415, 866512424138199907⟩, true⟩

def words05 : List Nat := [371284987115453125, 371284987252329536, 371284987332900012, 371284987334840845, 371284987089489589, 371284986936602688, 371284986930496173, 371284986932434283, 371284986677886650, 371284986417608374]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 57450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 57400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483122130219737, 362483170390665743⟩, ⟨102420115747807223, 104293663208605551⟩, true⟩

def words06 : List Nat := [371284986156480499, 371284986131039782, 371284985966054661, 371284985925964200, 371284985885254929, 371284985793589331, 371284985339696461, 371284985189855785, 371284985138288664, 371284985140330066]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 57460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 57400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478906755946017, 362478955034068631⟩, ⟨344718703486006148, 346593266910270834⟩, true⟩

def words07 : List Nat := [371284985110202705, 371284985079465546, 371284985215056520, 371284985257205383, 371284985304239568, 371284985351982518, 371284985353463871, 371284985311246838, 371284984942868695, 371284984840382311]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 57470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 57400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481032552357053, 362481080847747575⟩, ⟨222539124273448311, 224414680347752441⟩, true⟩

def words08 : List Nat := [371284984885923352, 371284984887863037, 371284984690764330, 371284984491882033, 371284984292246107, 371284984184832994, 371284984134836376, 371284984262712528, 371284984388623381, 371284984390630647]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 57480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 57400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502345649552738, 362502393962478851⟩, ⟨(-1002860766797073584), (-1000984202513385346)⟩, true⟩

def words09 : List Nat := [371284984346636395, 371284984371520715, 371284984698162689, 371284984802703978, 371284984860274726, 371284984918463904, 371284985130271656, 371284985235317214, 371284985539399970, 371284985844315456]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 57490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 57400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 57400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk574B
