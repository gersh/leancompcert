import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk939A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586645501706619, 360586703650622588⟩, ⟨(-440239506953881477), (-436552460710165305)⟩, true⟩

def state01 : KState := ⟨⟨360583551719283456, 360583609880994400⟩, ⟨(-149701740126719090), (-146013492370435774)⟩, true⟩

def words00 : List Nat := [360582054743079923, 360582054845467126, 360582054888982823, 360582054932646063, 360582054933803756, 360582054943027776, 360582055004747983, 360582055066723845, 360582055067936953, 360582055073864560]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360597803406841513, 360597861581406119⟩, ⟨(-1488130135673966973), (-1484440680766451567)⟩, true⟩

def words01 : List Nat := [360582055204826040, 360582055336218200, 360582055580478068, 360582055711929372, 360582055746317406, 360582055780799134, 360582055864669125, 360582056037075003, 360582056206480713, 360582056376172291]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591787095737202, 360591845283248703⟩, ⟨(-923114442482667517), (-919423771539596517)⟩, true⟩

def words02 : List Nat := [360582056488804246, 360582056514264694, 360582056652739806, 360582056791625601, 360582056844264128, 360582056899825779, 360582056901037351, 360582056891677233, 360582056888514288, 360582056994275525]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575469046527908, 360575527246869868⟩, ⟨609708815005396941, 613400691174443355⟩, true⟩

def words03 : List Nat := [360582057106686081, 360582057219355514, 360582057239407049, 360582057240767442, 360582057181111549, 360582057093284803, 360582057028976172, 360582057030342890, 360582057022103236, 360582056954035873]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595598350500431, 360595656563661685⟩, ⟨(-1281309916611455744), (-1277616836132812822)⟩, true⟩

def words04 : List Nat := [360582056929358593, 360582057054626115, 360582057245165432, 360582057435960994, 360582057530380519, 360582057536597414, 360582057539979431, 360582057543741862, 360582057660323759, 360582057806478337]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk939A
