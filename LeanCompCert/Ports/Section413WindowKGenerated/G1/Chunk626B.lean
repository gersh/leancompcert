import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk626A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk626B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk626A

def state06 : KState := ⟨⟨362484754964287372, 362484812729586539⟩, ⟨35041451715223007, 37486290608711673⟩, true⟩

def words05 : List Nat := [371285412203201201, 371285412080976548, 371285412087789220, 371285412089916668, 371285411882140075, 371285411636273822, 371285411389528816, 371285411248808969, 371285410985885211, 371285410978718501]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 62650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 62600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474103206493080, 362474160990974855⟩, ⟨702525273713408674, 704971314688180026⟩, true⟩

def words06 : List Nat := [371285410970761446, 371285410962388473, 371285410785370894, 371285410810853397, 371285410898515798, 371285410900643686, 371285410649023051, 371285410348025013, 371285410046191456, 371285409934882438]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 62660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 62600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362465546218739558, 362465604022428896⟩, ⟨1238841410538110047, 1241288655349840501⟩, true⟩

def words07 : List Nat := [371285409756859544, 371285409683314819, 371285409609033682, 371285409535097610, 371285409121218359, 371285408739856524, 371285408357403743, 371285408203243021, 371285407920134623, 371285407606592104]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 62670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 62600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478390418765568, 362478448241491705⟩, ⟨433773040366274124, 436221478503268076⟩, true⟩

def words08 : List Nat := [371285407292096468, 371285407162805442, 371285406929772540, 371285406942118720, 371285406943809979, 371285406907660660, 371285406627863288, 371285406603770723, 371285406629438477, 371285406631641702]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 62680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 62600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480566676319417, 362480624518453270⟩, ⟨297375748293445500, 299825403194387724⟩, true⟩

def words09 : List Nat := [371285406522237812, 371285406412613992, 371285406410396089, 371285406412766940, 371285406475017954, 371285406546235280, 371285406615779277, 371285406617913747, 371285406496439287, 371285406422810438]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 62690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 62600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 62600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk626B
