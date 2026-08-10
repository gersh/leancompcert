import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk800A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk800B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk800A

def state06 : KState := ⟨⟨362492346761673929, 362492442880178106⟩, ⟨(-587035450519442828), (-581839163013440994)⟩, true⟩

def words05 : List Nat := [371285175101870757, 371285175133820763, 371285175259530136, 371285175262310543, 371285175238961258, 371285175187365655, 371285175216227989, 371285175245524425, 371285175338211398, 371285175432069621]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 80050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 80000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479181551016958, 362479277694506396⟩, ⟨467006005592067315, 472204293541355233⟩, true⟩

def words06 : List Nat := [371285175524858068, 371285175527625533, 371285175412363038, 371285175389401847, 371285175371557704, 371285175374381505, 371285175292778480, 371285175209508206, 371285175125151470, 371285175087956395]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 80060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 80000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362471813044487146, 362471909212960756⟩, ⟨1057089954538818967, 1062290243095162563⟩, true⟩

def words07 : List Nat := [371285175098402806, 371285175183650660, 371285175233806631, 371285175236574602, 371285175078741026, 371285174968371006, 371285174898800615, 371285174901568673, 371285174738050751, 371285174575636770]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 80070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 80000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479709215924914, 362479805409133157⟩, ⟨424770993293731664, 429973262727415442⟩, true⟩

def words08 : List Nat := [371285174411865008, 371285174391221390, 371285174323148157, 371285174357915308, 371285174378777658, 371285174381549968, 371285174234333078, 371285174117775758, 371285174032346904, 371285174035212910]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 80080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 80000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479999373543253, 362480095591967990⟩, ⟨401520004590932711, 406724293740845785⟩, true⟩

def words09 : List Nat := [371285173970284550, 371285173874359016, 371285173777343580, 371285173753728843, 371285173672097311, 371285173636667870, 371285173600265067, 371285173564524835, 371285173358464102, 371285173298506578]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 80090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 80000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 80000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk800B
