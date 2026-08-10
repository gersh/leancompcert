import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk567A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk567B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk567A

def state06 : KState := ⟨⟨362500153954759158, 362500200983780231⟩, ⟨(-869519524769204399), (-867716311238240429)⟩, true⟩

def words05 : List Nat := [371284911991713997, 371284912134954152, 371284912425841033, 371284912563674571, 371284912794822948, 371284913026713483, 371284913257164452, 371284913259087460, 371284913519939456, 371284913791672301]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 56750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 56700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362493990449237999, 362494037495300652⟩, ⟨(-519647908067903490), (-517843727167488854)⟩, true⟩

def words06 : List Nat := [371284914321494487, 371284914473357405, 371284914540753811, 371284914608735894, 371284914770148959, 371284914777600179, 371284915094560341, 371284915412314335, 371284915708414527, 371284915871105773]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 56760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 56700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362506280349069554, 362506327412389583⟩, ⟨(-1217435422794246880), (-1215630262105504132)⟩, true⟩

def words07 : List Nat := [371284916118524050, 371284916366914881, 371284916924577229, 371284917069428187, 371284917164573991, 371284917260327556, 371284917483137735, 371284917552104667, 371284917930469618, 371284918309659700]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 56770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 56700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362501606309229502, 362501653389838268⟩, ⟨(-952036927440303645), (-950230785012134049)⟩, true⟩

def words08 : List Nat := [371284918688450771, 371284918860039568, 371284919341163654, 371284919823338911, 371284920353470636, 371284920470906542, 371284920561775683, 371284920653267860, 371284921026568252, 371284921323401472]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 56780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 56700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476662310231251, 362476709408107214⟩, ⟨464673348613265345, 466480471733344827⟩, true⟩

def words09 : List Nat := [371284921684524529, 371284922046405318, 371284922349933857, 371284922351847829, 371284922288323315, 371284922277681131, 371284922377335655, 371284922379282874, 371284922234880824, 371284922092468717]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 56790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 56700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 56700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk567B
