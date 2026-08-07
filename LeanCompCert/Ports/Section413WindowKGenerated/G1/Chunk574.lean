import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk574

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486406767780541, 362486454906192539⟩, ⟨(-86267613912650013), (-84401075481263427)⟩, true⟩

def state01 : KState := ⟨⟨362479443031550409, 362479491187291636⟩, ⟨313599865500816649, 315467398716078349⟩, true⟩

def words00 : List Nat := [371284984810836634, 371284984942804990, 371284985340847151, 371284985739645288, 371284986082642305, 371284986084578742, 371284986048887307, 371284986077329050, 371284986175684609, 371284986177689060]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 57400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 57400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492419593196353, 362492467766567736⟩, ⟨(-431426075616271488), (-429557530164707996)⟩, true⟩

def words01 : List Nat := [371284986083437214, 371284985991725551, 371284986109123221, 371284986209484058, 371284986400507022, 371284986592281641, 371284986781963044, 371284986783904111, 371284986790097338, 371284986922796909]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 57410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 57400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477757485022966, 362477805675656907⟩, ⟨410519413604627035, 412388950362694957⟩, true⟩

def words02 : List Nat := [371284987128559739, 371284987130496747, 371284986931978354, 371284986732764350, 371284986532791193, 371284986425306985, 371284986258364153, 371284986328105317, 371284986397147581, 371284986399152688]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 57420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 57400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362497591142427528, 362497639350583590⟩, ⟨(-728651962063055294), (-726781418920251348)⟩, true⟩

def words03 : List Nat := [371284986275445687, 371284986232654825, 371284986413876544, 371284986415823705, 371284986390484111, 371284986281807595, 371284986284658766, 371284986286813462, 371284986468523954, 371284986691003843]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 57430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 57400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477163019797477, 362477211245443781⟩, ⟨444852140346257728, 446723688219003486⟩, true⟩

def words04 : List Nat := [371284986892771261, 371284986925845905, 371284987108102739, 371284987291330883, 371284987565024369, 371284987566962199, 371284987436724410, 371284987304644328, 371284987171787410, 371284987114690413]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 57440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 57400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk574
