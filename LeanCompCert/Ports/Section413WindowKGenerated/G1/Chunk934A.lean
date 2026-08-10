import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk934A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485847787137787, 362485980169473668⟩, ⟨(-86310885443326801), (-77962743727503629)⟩, true⟩

def state01 : KState := ⟨⟨362484078073355341, 362484210485004702⟩, ⟨78982060118350767, 87332939861364039⟩, true⟩

def words00 : List Nat := [371285145483892181, 371285145487528741, 371285145480450473, 371285145510148737, 371285145529007305, 371285145532276416, 371285145398015687, 371285145380239568, 371285145423702014, 371285145427086507]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 93400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 93400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486311480382172, 362486443921779805⟩, ⟨(-129656842523295520), (-121303183843682794)⟩, true⟩

def words01 : List Nat := [371285145419544035, 371285145400549121, 371285145462945863, 371285145492178051, 371285145503725055, 371285145516507639, 371285145527815985, 371285145531101149, 371285145446477609, 371285145464432489]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 93410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 93400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482414483136593, 362482546953673813⟩, ⟨234448976756815609, 242805357811165905⟩, true⟩

def words02 : List Nat := [371285145581594366, 371285145604546101, 371285145607011652, 371285145600597301, 371285145595221251, 371285145598830140, 371285145624411696, 371285145696919965, 371285145744656673, 371285145748041909]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 93420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 93400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500603772257424, 362500736272402517⟩, ⟨(-1465058564202357896), (-1456699416740139960)⟩, true⟩

def words03 : List Nat := [371285145770380631, 371285145822259523, 371285145976041048, 371285146048789970, 371285146102885984, 371285146158033210, 371285146311574565, 371285146422638956, 371285146591701955, 371285146762265210]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 93430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 93400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481950996024670, 362482083525703787⟩, ⟨277932263325014743, 286294170597578921⟩, true⟩

def words04 : List Nat := [371285146931218768, 371285146982731161, 371285147080369095, 371285147179645646, 371285147283520289, 371285147286790870, 371285147238163702, 371285147189389690, 371285147139264953, 371285147133735864]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 93440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 93400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk934A
