import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk964A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk964B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk964A

def state06 : KState := ⟨⟨362486466781177404, 362486608332244604⟩, ⟨(-136850841475519086), (-127632230714593554)⟩, true⟩

def words05 : List Nat := [371285284529675116, 371285284691881724, 371285284831226357, 371285284855200132, 371285284901883149, 371285284950269897, 371285285104493994, 371285285149874987, 371285285166139160, 371285285183710849]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 96450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 96400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495589835587870, 362495731416902111⟩, ⟨(-1016882490904710687), (-1007660962356542857)⟩, true⟩

def words06 : List Nat := [371285285307338578, 371285285386635894, 371285285543457811, 371285285701694393, 371285285836741632, 371285285840125246, 371285285883835674, 371285285930784542, 371285286083611001, 371285286195412166]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 96460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 96400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493162197959898, 362493303810152950⟩, ⟨(-782674178424386118), (-773449670848380564)⟩, true⟩

def words07 : List Nat := [371285286304123670, 371285286413983640, 371285286571752005, 371285286691862334, 371285286813446295, 371285286936285643, 371285287057595261, 371285287060979278, 371285287121883444, 371285287209259009]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 96470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 96400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483414658818418, 362483556301172350⟩, ⟨157804145057633252, 167031562714238398⟩, true⟩

def words08 : List Nat := [371285287305789645, 371285287309181076, 371285287294689619, 371285287275862735, 371285287255772820, 371285287250476560, 371285287260048757, 371285287321236251, 371285287374077659, 371285287377581452]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 96480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 96400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497716277783521, 362497857950694997⟩, ⟨(-1222223460034589820), (-1212993093729688002)⟩, true⟩

def words09 : List Nat := [371285287433833162, 371285287509782689, 371285287691521494, 371285287731128012, 371285287741911480, 371285287753750890, 371285287871705649, 371285287937735288, 371285288070300078, 371285288204332476]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 96490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 96400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 96400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk964B
