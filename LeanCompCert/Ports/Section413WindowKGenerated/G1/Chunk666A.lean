import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk666A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493289226657337, 362493354798234726⟩, ⟨(-525764992971346348), (-522815465412775522)⟩, true⟩

def state01 : KState := ⟨⟨362482417641027121, 362482483232811031⟩, ⟨198363231942371012, 201314105361792904⟩, true⟩

def words00 : List Nat := [371285505178614128, 371285505223639731, 371285505257509999, 371285505292125338, 371285505297367854, 371285505299877798, 371285505310592362, 371285505410694026, 371285505510978365, 371285505513329899]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 66600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 66600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500653786063875, 362500719398392672⟩, ⟨(-1016409753419281012), (-1013457511400800324)⟩, true⟩

def words01 : List Nat := [371285505610992515, 371285505755235617, 371285506066147165, 371285506145276714, 371285506187719133, 371285506230904661, 371285506498177199, 371285506654512292, 371285506884432740, 371285507115307747]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 66610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 66600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486747690880511, 362486813323702278⟩, ⟨(-89983550146736696), (-87029942780022026)⟩, true⟩

def words02 : List Nat := [371285507338026327, 371285507340298659, 371285507326965099, 371285507393911968, 371285507474469448, 371285507476781475, 371285507369860662, 371285507223884885, 371285507153576469, 371285507175771435]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 66620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 66600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479444751573502, 362479510404926966⟩, ⟨396675230851378435, 399630206345822411⟩, true⟩

def words03 : List Nat := [371285507359810474, 371285507544786570, 371285507678856771, 371285507681129517, 371285507515086102, 371285507419226469, 371285507399717030, 371285507402016213, 371285507344116347, 371285507256762888]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 66630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 66600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487641907683457, 362487707581344491⟩, ⟨(-149544136268514286), (-146587807372013424)⟩, true⟩

def words04 : List Nat := [371285507279108689, 371285507302902783, 371285507550583601, 371285507799161092, 371285508010474714, 371285508012748678, 371285508016074214, 371285508066818043, 371285508212033552, 371285508247390432]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 66640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 66600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk666A
