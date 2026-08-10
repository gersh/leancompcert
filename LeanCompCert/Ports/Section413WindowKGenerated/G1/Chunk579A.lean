import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk579A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362475357136850290, 362475406151408827⟩, ⟨552556986569815468, 554474035289900802⟩, true⟩

def state01 : KState := ⟨⟨362478689505241809, 362478738537218340⟩, ⟨359664164305887155, 361582221616044201⟩, true⟩

def words00 : List Nat := [371284982528773293, 371284982530742384, 371284982458889762, 371284982386300835, 371284982312889443, 371284982293678043, 371284982219723680, 371284982317293464, 371284982400185945, 371284982402209120]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 57900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 57900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498051552343292, 362498100602037330⟩, ⟨(-761713984600394392), (-759794901183116254)⟩, true⟩

def words01 : List Nat := [371284982310303236, 371284982327226294, 371284982562538037, 371284982564495658, 371284982479961172, 371284982329193220, 371284982323233409, 371284982366103750, 371284982593922686, 371284982822627736]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 57910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 57900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487286092768900, 362487335160079564⟩, ⟨(-138183225975970788), (-136263122111325032)⟩, true⟩

def words02 : List Nat := [371284983044503339, 371284983046458283, 371284982992027514, 371284983115676448, 371284983245557569, 371284983247525760, 371284983111547791, 371284982974770870, 371284982954809900, 371284982997643022]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 57920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 57900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362463635624787246, 362463684709705414⟩, ⟨1232095086510970425, 1234016210467599223⟩, true⟩

def words03 : List Nat := [371284983258166189, 371284983519490971, 371284983743998699, 371284983745954217, 371284983612907761, 371284983570589161, 371284983564402145, 371284983566357996, 371284983249277980, 371284982883859153]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 57930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 57900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493335811667276, 362493384914088120⟩, ⟨(-488864405349078047), (-486942267198743237)⟩, true⟩

def words04 : List Nat := [371284982517608688, 371284982349120389, 371284982079437242, 371284982095153791, 371284982096667438, 371284982067047306, 371284981809967303, 371284981832170718, 371284982111932349, 371284982258962260]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 57940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 57900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk579A
