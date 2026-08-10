import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk885A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk885B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk885A

def state06 : KState := ⟨⟨362471105092767644, 362471223622412128⟩, ⟨1228928386968346640, 1236015887592168400⟩, true⟩

def words05 : List Nat := [371285181126904344, 371285181051409824, 371285180976514221, 371285180979914768, 371285180920282173, 371285180894387611, 371285180867503204, 371285180816716100, 371285180595068432, 371285180441377713]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362462446854335724, 362462565411444797⟩, ⟨1995725838488149978, 2002815771521565974⟩, true⟩

def words06 : List Nat := [371285180285889268, 371285180176195646, 371285179895863991, 371285179610980444, 371285179324890733, 371285179078976330, 371285178780962005, 371285178592369726, 371285178402744388, 371285178212297474]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477030020390763, 362477148605412772⟩, ⟨703988625780299593, 711081031197616953⟩, true⟩

def words07 : List Nat := [371285177959119803, 371285177760531623, 371285177560357675, 371285177452703748, 371285177191796461, 371285176911682030, 371285176630272642, 371285176459267964, 371285176249961020, 371285176162775581]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362464801135003339, 362464919747829143⟩, ⟨1787247685719972099, 1794342554145101649⟩, true⟩

def words08 : List Nat := [371285176074458636, 371285175986915658, 371285175776365380, 371285175632779420, 371285175487679634, 371285175349284629, 371285175040384999, 371285174720574118, 371285174399541461, 371285174207182853]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362460285832849346, 362460404473552948⟩, ⟨2187343827842716687, 2194441166100379939⟩, true⟩

def words09 : List Nat := [371285173980647133, 371285173882708405, 371285173783628094, 371285173685337883, 371285173471912603, 371285173271071055, 371285173068630630, 371285172961179488, 371285172708588181, 371285172432538280]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk885B
