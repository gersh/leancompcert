import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk307A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360513174883344008, 360513180563255707⟩, ⟨2152898923303750002, 2153016845749151244⟩, true⟩

def state01 : KState := ⟨⟨360579038604988288, 360579044288756261⟩, ⟨130636887285517842, 130754928137160332⟩, true⟩

def words00 : List Nat := [360583309121150976, 360583307000928813, 360583305874304076, 360583305804422734, 360583305734513846, 360583304669571075, 360583303309337284, 360583303005659560, 360583302701884143, 360583302020053466]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 30700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 30700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360542396481943593, 360542402169594466⟩, ⟨1256258644186509703, 1256376804302325183⟩, true⟩

def words01 : List Nat := [360583301881778646, 360583301069749981, 360583300501468899, 360583301278634858, 360583301788355554, 360583302298116528, 360583302298483451, 360583302268707419, 360583301182909346, 360583299852026183]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 30710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 30700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360545770512277875, 360545776203776636⟩, ⟨1152379817023726231, 1152498095365733003⟩, true⟩

def words02 : List Nat := [360583298521095154, 360583297813510194, 360583296050124877, 360583293292313769, 360583290534616116, 360583287495512941, 360583285014355137, 360583283588588864, 360583282162870381, 360583280209483299]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 30720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 30700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360602083424952312, 360602089120302146⟩, ⟨(-578397202163900406), (-578278805459512440)⟩, true⟩

def words03 : List Nat := [360583278989417020, 360583278536098528, 360583278380012920, 360583278618139147, 360583278618518950, 360583277970569954, 360583277322589757, 360583276647394283, 360583277187365947, 360583277799738095]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 30730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 30700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360565098825551622, 360565104524789970⟩, ⟨558468968886732711, 558587485142668873⟩, true⟩

def words04 : List Nat := [360583277885129043, 360583277885538205, 360583277920302191, 360583278303286630, 360583278303632463, 360583277746692835, 360583276135373848, 360583273833951683, 360583271532601266, 360583269971461277]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 30740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 30700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk307A
