import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk967A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489052338948694, 362489194622358358⟩, ⟨(-385460057609446366), (-376170717113766126)⟩, true⟩

def state01 : KState := ⟨⟨362490491694621853, 362490634008360256⟩, ⟨(-524643364443188709), (-515351091001968199)⟩, true⟩

def words00 : List Nat := [371285304657549292, 371285304684625488, 371285304817318197, 371285304951438799, 371285305058313880, 371285305061706247, 371285305043807851, 371285305066016495, 371285305175443236, 371285305234063620]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 96700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 96700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482048871278909, 362482191216025160⟩, ⟨291936956166397737, 301232228523567337⟩, true⟩

def words01 : List Nat := [371285305291313096, 371285305349829107, 371285305474146706, 371285305548061147, 371285305622094724, 371285305697391205, 371285305769409293, 371285305772803913, 371285305721086410, 371285305693160433]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 96710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 96700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480905846996135, 362481048221933131⟩, ⟨402499605293553692, 411797797855362278⟩, true⟩

def words02 : List Nat := [371285305733847478, 371285305737240522, 371285305677995270, 371285305597641713, 371285305516023504, 371285305460594150, 371285305381619363, 371285305395808056, 371285305406437794, 371285305409960169]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 96720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 96700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362499455771753960, 362499598177371737⟩, ⟨(-1391942274582968381), (-1382641114110400515)⟩, true⟩

def words03 : List Nat := [371285305431234972, 371285305498280962, 371285305590491543, 371285305593907966, 371285305590723053, 371285305572374939, 371285305637507110, 371285305682009720, 371285305832051665, 371285305983636812]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 96730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 96700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491178046795090, 362491320483038891⟩, ⟨(-591153991975096234), (-581849868588099116)⟩, true⟩

def words04 : List Nat := [371285306133410969, 371285306141540659, 371285306243142453, 371285306346537417, 371285306454092224, 371285306469798790, 371285306472386261, 371285306456608389, 371285306526994121, 371285306593067851]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 96740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 96700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk967A
