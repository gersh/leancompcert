import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk988A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk988B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk988A

def state06 : KState := ⟨⟨362473428923802195, 362473577886524908⟩, ⟨1154105065117237686, 1164047537776783130⟩, true⟩

def words05 : List Nat := [371285352733943943, 371285352786871425, 371285352836922273, 371285352840461299, 371285352822955243, 371285352816767448, 371285352823916996, 371285352827390285, 371285352708798936, 371285352593562910]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 98850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 98800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479485146570087, 362479634140418378⟩, ⟨555351705302862612, 565297255193785668⟩, true⟩

def words06 : List Nat := [371285352476857528, 371285352386352146, 371285352243297424, 371285352195576886, 371285352146765579, 371285352089229599, 371285351894221168, 371285351803412247, 371285351718041665, 371285351721638099]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 98860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 98800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478150642164820, 362478299667695730⟩, ⟨687329941186400011, 697278623694849787⟩, true⟩

def words07 : List Nat := [371285351666405248, 371285351612228621, 371285351600931884, 371285351604800007, 371285351601631259, 371285351606335874, 371285351608935570, 371285351604352407, 371285351500670386, 371285351433712062]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 98870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 98800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481494253967063, 362481643310452078⟩, ⟨356711465337701623, 366663208748572527⟩, true⟩

def words08 : List Nat := [371285351381606616, 371285351385142485, 371285351320406972, 371285351256901633, 371285351192096374, 371285351159504794, 371285351089219846, 371285351107851303, 371285351110500189, 371285351098992361]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 98880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 98800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362500010419323067, 362500159507171300⟩, ⟨(-1474460289040340086), (-1464505443965758900)⟩, true⟩

def words09 : List Nat := [371285351094094852, 371285351128485713, 371285351263352927, 371285351272187473, 371285351274881606, 371285351270338655, 371285351358119430, 371285351409404530, 371285351561488330, 371285351715096744]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 98890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 98800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 98800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk988B
