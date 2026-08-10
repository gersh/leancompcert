import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk786A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588694443955487, 360588734628323380⟩, ⟨(-511897590239703617), (-509764364018126571)⟩, true⟩

def state01 : KState := ⟨⟨360595985829019540, 360596026023975304⟩, ⟨(-1085109567024839932), (-1082975508544125072)⟩, true⟩

def words00 : List Nat := [360582249367332904, 360582249414231751, 360582249415251764, 360582249335459613, 360582249255486132, 360582249116627208, 360582249247967813, 360582249395118807, 360582249461177822, 360582249637610239]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 78600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 78600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360599853269772721, 360599893475318741⟩, ⟨(-1389153510842026362), (-1387018619806927610)⟩, true⟩

def words01 : List Nat := [360582249861777124, 360582250086263611, 360582250438800845, 360582250715869284, 360582250856210878, 360582250996627275, 360582251052996789, 360582251190595599, 360582251415903755, 360582251641460015]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 78610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 78600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591328217345732, 360591368433592301⟩, ⟨(-718956266845020679), (-716820534480257483)⟩, true⟩

def words02 : List Nat := [360582251776760038, 360582251842466622, 360582252069508138, 360582252296914029, 360582252403859555, 360582252404982664, 360582252350575165, 360582252215384535, 360582252079974843, 360582252174935026]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 78620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 78600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360559085875598208, 360559126102431221⟩, ⟨1816410475494816124, 1818547040325942612⟩, true⟩

def words03 : List Nat := [360582252253332793, 360582252331927602, 360582252332937801, 360582252330041682, 360582252165575090, 360582251960944909, 360582251755995921, 360582251528286385, 360582251357697417, 360582251064795488]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 78630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 78600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586155710897256, 360586195948337624⟩, ⟨(-312514840554735485), (-310377441511087781)⟩, true⟩

def words04 : List Nat := [360582250771648317, 360582250550566700, 360582250499466083, 360582250555320795, 360582250556375338, 360582250460964712, 360582250203989246, 360582249961066817, 360582249717819689, 360582249686478130]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 78640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 78600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk786A
