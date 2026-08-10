import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk665A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk665B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk665A

def state06 : KState := ⟨⟨362505289009165673, 362505354498754506⟩, ⟨(-1324261959761641913), (-1321317891005853017)⟩, true⟩

def words05 : List Nat := [371285501439958737, 371285501631487760, 371285502047287046, 371285502188164471, 371285502265898009, 371285502344333066, 371285502560950465, 371285502665550105, 371285502965344594, 371285503266185797]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 66550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 66500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488226680470123, 362488292190545954⟩, ⟨(-188588303689861565), (-185642871214405979)⟩, true⟩

def words06 : List Nat := [371285503522322695, 371285503535011822, 371285503602647510, 371285503671431147, 371285503808311275, 371285503810581515, 371285503676994396, 371285503544421658, 371285503501247674, 371285503545772488]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 66560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 66500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473465589315742, 362473531119804588⟩, ⟨794216436439899084, 797163227913304670⟩, true⟩

def words07 : List Nat := [371285503814585302, 371285504084316391, 371285504346227709, 371285504348498185, 371285504335798891, 371285504364595325, 371285504486561131, 371285504488831659, 371285504310443231, 371285504133140625]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 66570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 66500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485795955537639, 362485861506348434⟩, ⟨(-26759514006813042), (-23811369395898442)⟩, true⟩

def words08 : List Nat := [371285503984331753, 371285503986859902, 371285503943241176, 371285503980980928, 371285503982740818, 371285503973855603, 371285503762439502, 371285503771281410, 371285503922237810, 371285503929958293]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 66580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 66500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493289226657337, 362493354798234726⟩, ⟨(-525764992971346348), (-522815465412775522)⟩, true⟩

def words09 : List Nat := [371285503931702478, 371285503888332452, 371285504023352794, 371285504126573134, 371285504282038615, 371285504438345134, 371285504594213340, 371285504596524897, 371285504713306225, 371285504834038802]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 66590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 66500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 66500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk665B
