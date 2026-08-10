import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk998A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk998B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk998A

def state06 : KState := ⟨⟨362493651526429765, 362493803635169014⟩, ⟨(-853381582571113002), (-843126518636320624)⟩, true⟩

def words05 : List Nat := [371285360536809919, 371285360558109592, 371285360643942268, 371285360647453554, 371285360599983078, 371285360529807742, 371285360470693971, 371285360474601325, 371285360545750390, 371285360634211320]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487384667987249, 362487536808440555⟩, ⟨(-227538530464150652), (-217280299403000622)⟩, true⟩

def words06 : List Nat := [371285360721233869, 371285360726566290, 371285360808933127, 371285360893200407, 371285361005910006, 371285361045353353, 371285361083747759, 371285361123296576, 371285361173118775, 371285361198910231]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481290498166861, 362481442670283797⟩, ⟨381158985223193174, 391420378689804776⟩, true⟩

def words07 : List Nat := [371285361323377815, 371285361449323115, 371285361571911346, 371285361575423466, 371285361564188981, 371285361560452715, 371285361647164811, 371285361650677165, 371285361611989101, 371285361576758465]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483737018951146, 362483889222518286⟩, ⟨136816823100853697, 147081357977154477⟩, true⟩

def words08 : List Nat := [371285361600952666, 371285361623601893, 371285361672101865, 371285361721952861, 371285361755205478, 371285361758717989, 371285361658017807, 371285361641694750, 371285361652074508, 371285361655774640]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483079420242978, 362483231655782529⟩, ⟨202515851157391177, 212783579914956903⟩, true⟩

def words09 : List Nat := [371285361643702060, 371285361612595527, 371285361638641203, 371285361651074320, 371285361692358465, 371285361735020027, 371285361747472249, 371285361750985405, 371285361638503063, 371285361621547444]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk998B
