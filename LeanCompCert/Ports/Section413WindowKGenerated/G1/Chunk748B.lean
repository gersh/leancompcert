import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk748A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk748B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk748A

def state06 : KState := ⟨⟨362470391273697698, 362470474877491531⟩, ⟨1101239373968560531, 1105465881207304955⟩, true⟩

def words05 : List Nat := [371285243282752402, 371285243224049150, 371285243164519000, 371285243104933083, 371285242873815651, 371285242649653160, 371285242424138401, 371285242377760441, 371285242182237166, 371285241987846959]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 74850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 74800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489240977183594, 362489324604024771⟩, ⟨(-309908529493526673), (-305680296812205397)⟩, true⟩

def words06 : List Nat := [371285241792333263, 371285241776184835, 371285241710893555, 371285241754500148, 371285241757369324, 371285241759964105, 371285241633962355, 371285241627096243, 371285241787189296, 371285241844387366]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 74860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 74800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484256071644145, 362484339722045824⟩, ⟨63383956210574859, 67613952976359933⟩, true⟩

def words07 : List Nat := [371285241880339707, 371285241917213390, 371285242131156457, 371285242257048162, 371285242431578806, 371285242607066380, 371285242746180738, 371285242748759370, 371285242694943430, 371285242686161428]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 74870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 74800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478113433727355, 362478197107058226⟩, ⟨523389385378844235, 527621099202082553⟩, true⟩

def words08 : List Nat := [371285242821243286, 371285242823819744, 371285242733512383, 371285242636337153, 371285242538205464, 371285242455029324, 371285242333604001, 371285242363932974, 371285242385459043, 371285242388126488]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 74880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 74800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490122920707945, 362490206617339882⟩, ⟨(-376060764866886655), (-371827305911435463)⟩, true⟩

def words09 : List Nat := [371285242379857346, 371285242466968175, 371285242594969565, 371285242597546468, 371285242488191647, 371285242350841153, 371285242250341826, 371285242253217334, 371285242297914735, 371285242367117436]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 74890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 74800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 74800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk748B
