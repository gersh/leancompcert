import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk440A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362507413699004365, 362507441384266209⟩, ⟨(-964475856177198993), (-963652795192008009)⟩, true⟩

def state01 : KState := ⟨⟨362486928319513311, 362486956017904305⟩, ⟨(-63014388202416502), (-62190749466711734)⟩, true⟩

def words00 : List Nat := [371285541177682800, 371285541251921088, 371285541775605796, 371285542300006537, 371285542930124635, 371285542931578959, 371285542873583650, 371285542815321634, 371285542911265181, 371285542945048276]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 44000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 44000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362475666605436400, 362475694316910135⟩, ⟨432707089745680955, 433531304319594833⟩, true⟩

def words01 : List Nat := [371285543243226288, 371285543541961700, 371285543778154102, 371285543779608903, 371285543399889815, 371285543176555581, 371285543243391317, 371285543244852831, 371285543046616766, 371285542824504856]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 44010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 44000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362502917835390779, 362502945559901980⟩, ⟨(-767013564422240873), (-766188775872700301)⟩, true⟩

def words02 : List Nat := [371285542894065257, 371285543072524250, 371285543378279639, 371285543684605631, 371285543893199681, 371285543894654776, 371285543451437753, 371285543489037709, 371285544041765280, 371285544438513125]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 44020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 44000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362497876868547631, 362497904606317148⟩, ⟨(-545004016557046846), (-544178644177068274)⟩, true⟩

def words03 : List Nat := [371285544837285531, 371285545236546712, 371285545899996776, 371285546338975714, 371285546932851898, 371285547527244661, 371285548004579466, 371285548006035307, 371285548141192298, 371285548423574316]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 44030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 44000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489743476260662, 362489771227006812⟩, ⟨(-186688457220020021), (-185862513281656827)⟩, true⟩

def words04 : List Nat := [371285549220708055, 371285549531541817, 371285549831776146, 371285550132519764, 371285550491655835, 371285550595768645, 371285551021307751, 371285551447435012, 371285551872188668, 371285551969480726]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 44040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 44000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk440A
