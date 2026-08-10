import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk647A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494439056761756, 362494500799772260⟩, ⟨(-582293259864806019), (-579595096859811967)⟩, true⟩

def state01 : KState := ⟨⟨362491926071016621, 362491987833943968⟩, ⟨(-419724185651078088), (-417024733924464434)⟩, true⟩

def words00 : List Nat := [371285542855788784, 371285542858011557, 371285542981101702, 371285543149067516, 371285543388725229, 371285543390927202, 371285543312488766, 371285543234460404, 371285543313808631, 371285543415932742]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 64700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 64700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483735126102958, 362483796908863844⟩, ⟨110426954368867669, 113127689625956673⟩, true⟩

def words01 : List Nat := [371285543725099499, 371285544035171756, 371285544287327426, 371285544373955560, 371285544462102503, 371285544551283431, 371285544878001667, 371285544887349396, 371285544889018182, 371285544864513195]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 64710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 64700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488597052264819, 362488658854770781⟩, ⟨(-204172917014370332), (-201470903758103554)⟩, true⟩

def words02 : List Nat := [371285545015015297, 371285545125459345, 371285545432249099, 371285545739920887, 371285546009159442, 371285546011362240, 371285546064584559, 371285546169443162, 371285546371357378, 371285546421720804]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 64720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 64700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483660892452826, 362483722715006619⟩, ⟨115397534029010804, 118100845082160784⟩, true⟩

def words03 : List Nat := [371285546471125972, 371285546521253046, 371285546744301743, 371285546849153862, 371285546958879626, 371285547069514529, 371285547179407389, 371285547181610424, 371285546973478520, 371285546948016848]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 64730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 64700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479743990479317, 362479805832674040⟩, ⟨368982801289339789, 371687383997695021⟩, true⟩

def words04 : List Nat := [371285547096194149, 371285547098397446, 371285546957122668, 371285546770331172, 371285546582684658, 371285546418924767, 371285546177693398, 371285546175749201, 371285546176048315, 371285546178372847]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 64740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 64700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk647A
