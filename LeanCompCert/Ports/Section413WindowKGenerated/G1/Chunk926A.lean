import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk926A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362495444554484781, 362495574592083253⟩, ⟨(-976670495121208065), (-968540415604000353)⟩, true⟩

def state01 : KState := ⟨⟨362480921428529003, 362481051495396961⟩, ⟨368207622363526102, 376340412382727846⟩, true⟩

def words00 : List Nat := [371285115421226537, 371285115424465125, 371285115391378589, 371285115401824854, 371285115446436906, 371285115449682670, 371285115374000936, 371285115299190608, 371285115223031626, 371285115207872750]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 92600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 92600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362465881271607867, 362466011367576975⟩, ⟨1761209617746092575, 1769345102971853327⟩, true⟩

def words01 : List Nat := [371285115213079246, 371285115263469285, 371285115312516539, 371285115315755410, 371285115209294480, 371285115140223851, 371285115069473447, 371285115034178731, 371285114842743650, 371285114640120399]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 92610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 92600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482178742845746, 362482308867800101⟩, ⟨251672582955788102, 259810752939258172⟩, true⟩

def words02 : List Nat := [371285114436067799, 371285114317307551, 371285114144877885, 371285114090403109, 371285114034836487, 371285113975653525, 371285113789246359, 371285113721049709, 371285113687428889, 371285113690783360]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 92620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 92600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486270633273263, 362486400787807054⟩, ⟨(-127413817255618372), (-119272907179804778)⟩, true⟩

def words03 : List Nat := [371285113662984170, 371285113594405365, 371285113525844603, 371285113529415023, 371285113474927662, 371285113444736663, 371285113413507378, 371285113382037557, 371285113295540017, 371285113313501080]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 92630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 92600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487782928095003, 362487913111462501⟩, ⟨(-267498630075133173), (-259355048696311301)⟩, true⟩

def words04 : List Nat := [371285113446080775, 371285113475476331, 371285113503788520, 371285113533179017, 371285113565982907, 371285113569587388, 371285113632315452, 371285113724363805, 371285113809134113, 371285113842715307]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 92640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 92600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk926A
