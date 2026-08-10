import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk549A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk549B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk549A

def state06 : KState := ⟨⟨362490197168148641, 362490241148225193⟩, ⟨(-294381144570081446), (-292748261192867668)⟩, true⟩

def words05 : List Nat := [371284913310977264, 371284913372559108, 371284913732018438, 371284913949822546, 371284914225349836, 371284914501569815, 371284914710141935, 371284914711989978, 371284914576384697, 371284914675613835]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 54950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 54900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362467623447469764, 362467667444000213⟩, ⟨946387271797477482, 948021059566941900⟩, true⟩

def words06 : List Nat := [371284914918486335, 371284914920334470, 371284914722447889, 371284914540597771, 371284914358019726, 371284914277404809, 371284914030357349, 371284913886348450, 371284913741705227, 371284913597530629]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 54960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 54900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362492275451776084, 362492319465028886⟩, ⟨(-408899354997984013), (-407264647916838975)⟩, true⟩

def words07 : List Nat := [371284913285074834, 371284913110794793, 371284913089614395, 371284913091463008, 371284912806239421, 371284912470296963, 371284912133595030, 371284912017292033, 371284911957551655, 371284912094338706]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 54970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 54900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475889523518409, 362475933553448888⟩, ⟨492038779470611044, 493674403573850524⟩, true⟩

def words08 : List Nat := [371284912187761203, 371284912189610930, 371284911944079566, 371284911988133500, 371284912046702542, 371284912048555391, 371284911764386275, 371284911481300486, 371284911197498288, 371284911083973963]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 54980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 54900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362459451612604065, 362459495659219944⟩, ⟨1396138910642510108, 1397775452359787194⟩, true⟩

def words09 : List Nat := [371284911053439923, 371284911186966561, 371284911291266613, 371284911293117119, 371284911024397674, 371284910788126955, 371284910583941792, 371284910585791190, 371284910218326493, 371284909758353759]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 54990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 54900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 54900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk549B
