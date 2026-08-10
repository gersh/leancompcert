import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk574A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk574A
