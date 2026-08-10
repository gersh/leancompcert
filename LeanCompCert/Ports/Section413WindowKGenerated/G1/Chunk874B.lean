import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk874A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk874B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk874A

def state06 : KState := ⟨⟨362470837428496061, 362470952920320415⟩, ⟨1237617737996066343, 1244437875947801771⟩, true⟩

def words05 : List Nat := [371285182504221419, 371285182481677922, 371285182458158889, 371285182426116431, 371285182237783599, 371285182091098499, 371285181942797467, 371285181891747476, 371285181731297914, 371285181572000587]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 87450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 87400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474197798451261, 362474313317504978⟩, ⟨943728259339870871, 950550778908143391⟩, true⟩

def words06 : List Nat := [371285181411393526, 371285181319457401, 371285181172125571, 371285181138889330, 371285181104707896, 371285181024946927, 371285180782175398, 371285180651115012, 371285180518512366, 371285180480862794]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 87460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 87400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474104854578955, 362474220401475745⟩, ⟨951897573922766326, 958722529057661604⟩, true⟩

def words07 : List Nat := [371285180358922666, 371285180238472800, 371285180123341431, 371285180126697834, 371285180074515500, 371285180062189760, 371285180048866953, 371285180034166901, 371285179856808856, 371285179735369866]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 87470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 87400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478460143800644, 362478575717820958⟩, ⟨570896365883896486, 577723693926706822⟩, true⟩

def words08 : List Nat := [371285179617411304, 371285179620467670, 371285179524134753, 371285179403542770, 371285179281814112, 371285179201429836, 371285179071870234, 371285179057858563, 371285179042795943, 371285179028987111]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 87480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 87400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493619660354646, 362493735261906880⟩, ⟨(-755476000966651809), (-748646264016662813)⟩, true⟩

def words09 : List Nat := [371285179010595927, 371285179069229759, 371285179155514730, 371285179158582987, 371285179148632321, 371285179126175307, 371285179182871070, 371285179201292056, 371285179301146730, 371285179402385085]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 87490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 87400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 87400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk874B
