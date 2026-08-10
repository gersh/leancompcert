import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk830A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497611092371808, 362497714686632123⟩, ⟨(-1035865025607114747), (-1030059167463585693)⟩, true⟩

def state01 : KState := ⟨⟨362499082942275450, 362499186562481929⟩, ⟨(-1158079299676912048), (-1152271287866692766)⟩, true⟩

def words00 : List Nat := [371285304636932740, 371285304639811082, 371285304752803461, 371285304884343830, 371285305040482764, 371285305115280733, 371285305176538259, 371285305238784041, 371285305445021588, 371285305615524699]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 83000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 83000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484604181671615, 362484707827801154⟩, ⟨43884329504019617, 49694493321121289⟩, true⟩

def words01 : List Nat := [371285305843929867, 371285306073465169, 371285306255442869, 371285306258320752, 371285306277320209, 371285306311459572, 371285306418198382, 371285306421092610, 371285306416346973, 371285306412399096]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 83010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 83000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490791407786596, 362490895079667508⟩, ⟨(-469773270171708411), (-463960968348388793)⟩, true⟩

def words02 : List Nat := [371285306521925943, 371285306569943814, 371285306761882040, 371285306955025132, 371285307114493089, 371285307117371475, 371285307083188464, 371285307081888701, 371285307205204255, 371285307275493786]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 83020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 83000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489711383841486, 362489815081972947⟩, ⟨(-380056696503844361), (-374242214966520825)⟩, true⟩

def words03 : List Nat := [371285307342920314, 371285307411333333, 371285307598331142, 371285307734189503, 371285307913111157, 371285308093105355, 371285308268709415, 371285308271588254, 371285308307950977, 371285308365833131]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 83030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 83000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480976228269594, 362481079952073870⟩, ⟨345329055530868094, 351145669072924506⟩, true⟩

def words04 : List Nat := [371285308481693115, 371285308484572033, 371285308407314227, 371285308331063694, 371285308253728922, 371285308189785479, 371285308058015882, 371285308066886783, 371285308072718614, 371285308075723153]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 83040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 83000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk830A
