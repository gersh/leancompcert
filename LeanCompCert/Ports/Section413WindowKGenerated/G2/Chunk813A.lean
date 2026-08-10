import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk813A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592178780235697, 360592221885999614⟩, ⟨(-816934946850119674), (-814568131295219338)⟩, true⟩

def state01 : KState := ⟨⟨360589486267631482, 360589529384352116⟩, ⟨(-598076192345024236), (-595708485953802580)⟩, true⟩

def words00 : List Nat := [360582202807625679, 360582202911906099, 360582202923450592, 360582202935121374, 360582202936114090, 360582202812280886, 360582202866083872, 360582202969229767, 360582202996651000, 360582203087959823]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 81300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 81300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590605856954149, 360590648984683880⟩, ⟨(-689143979543086309), (-686775377948746217)⟩, true⟩

def words01 : List Nat := [360582203229969984, 360582203372347064, 360582203531455943, 360582203572193954, 360582203573283014, 360582203483548113, 360582203425590367, 360582203534616151, 360582203639428357, 360582203744488251]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 81310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 81300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592933474643232, 360592976613462019⟩, ⟨(-878569960368701267), (-876200456957180953)⟩, true⟩

def words02 : List Nat := [360582203773812104, 360582203774976625, 360582203696361810, 360582203641183378, 360582203585685443, 360582203490688409, 360582203447487462, 360582203328886968, 360582203214163007, 360582203347954929]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 81320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 81300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360584488263662799, 360584531413456143⟩, ⟨(-191614938191155694), (-189244542163050668)⟩, true⟩

def words03 : List Nat := [360582203632354182, 360582203916969591, 360582204084834172, 360582204229849327, 360582204336958057, 360582204444372947, 360582204672120216, 360582204796131814, 360582204825775186, 360582204855605084]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 81330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 81300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599128653082712, 360599171813866057⟩, ⟨(-1382535399034680804), (-1380164109025337994)⟩, true⟩

def words04 : List Nat := [360582204930111715, 360582205080837303, 360582205382154372, 360582205683688588, 360582205820269174, 360582205845033486, 360582205865743055, 360582205886777696, 360582206058399125, 360582206268156412]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 81340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 81300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk813A
