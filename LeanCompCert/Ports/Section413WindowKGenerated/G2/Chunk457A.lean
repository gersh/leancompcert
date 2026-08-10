import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk457A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590886842020790, 360590899847514766⟩, ⟨(-351591505017216813), (-351189866110113313)⟩, true⟩

def state01 : KState := ⟨⟨360618781061964767, 360618794073378860⟩, ⟨(-1626577065871967751), (-1626175156386077385)⟩, true⟩

def words00 : List Nat := [360583215722377249, 360583216351869639, 360583216968942358, 360583217586099734, 360583217734576631, 360583217735203097, 360583217554593386, 360583217703661978, 360583218155931145, 360583218934869835]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 45700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 45700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594706386038420, 360594719403420477⟩, ⟨(-525986312704787244), (-525584130393944262)⟩, true⟩

def words01 : List Nat := [360583219473559707, 360583220012288689, 360583220710559051, 360583221701191618, 360583222440164720, 360583223179211629, 360583223545634826, 360583223546261444, 360583223686811639, 360583223938964452]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 45710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 45700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360573304930880924, 360573317954162435⟩, ⟨452491484128080771, 452893936191953209⟩, true⟩

def words02 : List Nat := [360583224329836506, 360583224330463178, 360583224244170339, 360583223918241582, 360583223592214285, 360583223006579425, 360583222660596559, 360583222388731233, 360583222116814611, 360583221604636784]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 45720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 45700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599571167566157, 360599584196774668⟩, ⟨(-748988254877616175), (-748585531743718775)⟩, true⟩

def words03 : List Nat := [360583221388589397, 360583221056614589, 360583220724471966, 360583220380258697, 360583219896266052, 360583219006216180, 360583218116085325, 360583217735229467, 360583218093551634, 360583218451999877]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 45730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 45700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360556208966418690, 360556222001593727⟩, ⟨1234475148520894201, 1234878144592829037⟩, true⟩

def words04 : List Nat := [360583218541622641, 360583218542249619, 360583218155032748, 360583218128551613, 360583218101914924, 360583217748556593, 360583217059792745, 360583215972996005, 360583214886130264, 360583213873606686]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 45740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 45700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk457A
