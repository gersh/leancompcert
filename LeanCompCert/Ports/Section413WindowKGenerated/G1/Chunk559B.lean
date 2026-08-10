import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk559A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk559B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk559A

def state06 : KState := ⟨⟨362469334492157460, 362469380153116885⟩, ⟨868675681459526170, 870401789473080012⟩, true⟩

def words05 : List Nat := [371284934854832910, 371284935019844185, 371284935184054097, 371284935185937430, 371284934961406994, 371284934812149464, 371284934674634287, 371284934676550904, 371284934428035383, 371284934152213974]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 55950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 55900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489276818527144, 362489322496347857⟩, ⟨(-247353649425816994), (-245626597770110646)⟩, true⟩

def words06 : List Nat := [371284933884313209, 371284933886407751, 371284933888275308, 371284934041226518, 371284934120360785, 371284934122244438, 371284933775879404, 371284933749484773, 371284933954146747, 371284934034505652]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 55960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 55900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487280578784857, 362487326273779929⟩, ⟨(-135544585077774883), (-133816572084459801)⟩, true⟩

def words07 : List Nat := [371284934117647850, 371284934201425956, 371284934560447937, 371284934800045609, 371284935133331238, 371284935467340873, 371284935782317371, 371284935792063577, 371284935836075529, 371284935881109480]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 55970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 55900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486009691400143, 362486055403174233⟩, ⟨(-64420178042952641), (-62691225671865961)⟩, true⟩

def words08 : List Nat := [371284936052354102, 371284936054241102, 371284935881240710, 371284935708993249, 371284935536006584, 371284935461017184, 371284935427648361, 371284935571709157, 371284935715093647, 371284935737055181]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 55980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 55900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496544903597938, 362496590632453006⟩, ⟨(-654389120975458652), (-652659212157127280)⟩, true⟩

def words09 : List Nat := [371284935909860914, 371284936083646386, 371284936336679596, 371284936338564533, 371284936166865169, 371284935945598569, 371284935818941160, 371284935821045563, 371284936001480172, 371284936211779141]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 55990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 55900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 55900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk559B
