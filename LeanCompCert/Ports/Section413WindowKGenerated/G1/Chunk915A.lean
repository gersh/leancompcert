import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk915A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492899589403327, 362493026438549978⟩, ⟨(-732354391314333120), (-724517812851241048)⟩, true⟩

def state01 : KState := ⟨⟨362481992404021659, 362482119281636609⟩, ⟨265733653900995528, 273572837359805030⟩, true⟩

def words00 : List Nat := [371285108479859634, 371285108503955579, 371285108526110731, 371285108549432812, 371285108608001114, 371285108611525052, 371285108690856093, 371285108772691661, 371285108818675642, 371285108821985859]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 91500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 91500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491347492378024, 362491474398991826⟩, ⟨(-590425701932898501), (-582583864654639605)⟩, true⟩

def words01 : List Nat := [371285108791529523, 371285108783534526, 371285108881270474, 371285108884468019, 371285108835277962, 371285108768101208, 371285108708920661, 371285108712506277, 371285108749935063, 371285108823171472]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 91510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 91500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480913372899337, 362481040308333491⟩, ⟨364514449674806237, 372358924738711227⟩, true⟩

def words02 : List Nat := [371285108895471742, 371285108898670094, 371285108844386690, 371285108863792654, 371285108887557779, 371285108890755799, 371285108755546890, 371285108621299825, 371285108485715805, 371285108470954913]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 91520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 91500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362468831209798140, 362468958174028251⟩, ⟨1470482160915902859, 1478329271822192319⟩, true⟩

def words03 : List Nat := [371285108431097582, 371285108437004477, 371285108440284060, 371285108443482231, 371285108287553115, 371285108169821686, 371285108050390670, 371285108040409876, 371285107891036023, 371285107718181870]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 91530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 91500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489133930266169, 362489260923130089⟩, ⟨(-388095867464280108), (-380246135271717708)⟩, true⟩

def words04 : List Nat := [371285107543932031, 371285107490346909, 371285107422487958, 371285107441287918, 371285107443770010, 371285107429118258, 371285107355536449, 371285107370738684, 371285107493978520, 371285107542661589]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 91540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 91500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk915A
