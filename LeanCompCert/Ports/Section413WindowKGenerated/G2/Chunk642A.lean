import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk642A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588695130992372, 360588721512944564⟩, ⟨(-375311026610136214), (-374166886725015768)⟩, true⟩

def state01 : KState := ⟨⟨360566683605705491, 360566709996165051⟩, ⟨1037919122081633951, 1039063808181912531⟩, true⟩

def words00 : List Nat := [360582893569278461, 360582893570182033, 360582893516693465, 360582893341424314, 360582893165997714, 360582892929583192, 360582892866210996, 360582892724040866, 360582892581778937, 360582892270081605]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 64200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 64200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360596410986839522, 360596437385840239⟩, ⟨(-871135136049735753), (-869989901480362857)⟩, true⟩

def words01 : List Nat := [360582892018807722, 360582891761486366, 360582891503908210, 360582891438234286, 360582891207374231, 360582890765938595, 360582890324342548, 360582890148902976, 360582890360584021, 360582890572469530]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 64210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 64200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583052279767995, 360583078687364401⟩, ⟨(-13261599769845223), (-12115813141174219)⟩, true⟩

def words02 : List Nat := [360582890662409621, 360582890663313240, 360582890716078122, 360582890864200585, 360582890864970915, 360582890842896227, 360582890739277067, 360582890498963517, 360582890258489454, 360582890058615960]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 64220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 64200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360552452768218065, 360552479184339002⟩, ⟨1952390230044616427, 1953536564245415687⟩, true⟩

def words03 : List Nat := [360582890304436373, 360582890550439013, 360582890630442920, 360582890631346637, 360582890470027023, 360582890198945164, 360582889927606451, 360582889898570592, 360582889628208652, 360582889155762499]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 64230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 64200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597743485622324, 360597769910268718⟩, ⟨(-957313269201234991), (-956166387282980597)⟩, true⟩

def words04 : List Nat := [360582888683120046, 360582888406686362, 360582888277007418, 360582888229940745, 360582888182805271, 360582887931031235, 360582887785784724, 360582887783971531, 360582887942214760, 360582888174773816]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 64240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 64200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk642A
