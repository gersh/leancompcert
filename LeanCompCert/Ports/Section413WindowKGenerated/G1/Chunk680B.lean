import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk680A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk680B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk680A

def state06 : KState := ⟨⟨362503249715929597, 362503318309925206⟩, ⟨(-1219132051425293610), (-1215979015524999716)⟩, true⟩

def words05 : List Nat := [371285451025990120, 371285451083188165, 371285451354940767, 371285451447746966, 371285451515790281, 371285451584568715, 371285451713868702, 371285451763263173, 371285452027352207, 371285452292447870]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 68050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 68000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485378756011169, 362485447371025524⟩, ⟨(-2804073223896662), 350393318259134⟩, true⟩

def words06 : List Nat := [371285452519273571, 371285452521599193, 371285452558851205, 371285452659925254, 371285452825460006, 371285452827785706, 371285452705843101, 371285452584001842, 371285452515916711, 371285452518569498]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 68060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 68000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470743596302931, 362470812232262364⟩, ⟨993572311763592285, 996728204142309553⟩, true⟩

def words07 : List Nat := [371285452735607825, 371285452953683134, 371285453171125973, 371285453173452258, 371285453122843856, 371285453082580233, 371285453156365459, 371285453158691654, 371285452988203992, 371285452775801470]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 68070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 68000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480093420527467, 362480162077323307⟩, ⟨357036461737409615, 360193772766854469⟩, true⟩

def words08 : List Nat := [371285452562340827, 371285452492686140, 371285452389286044, 371285452436412082, 371285452438234070, 371285452424453292, 371285452150569226, 371285452093419368, 371285452040719803, 371285452043144527]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 68080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 68000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489166264406961, 362489234942374504⟩, ⟨(-260765333826775706), (-257606581112618396)⟩, true⟩

def words09 : List Nat := [371285451967193920, 371285451892198886, 371285451930100855, 371285451966398233, 371285452067421955, 371285452169417616, 371285452270754806, 371285452273081965, 371285452170336243, 371285452228741627]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 68090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 68000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 68000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk680B
