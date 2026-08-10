import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk645A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk645B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk645A

def state06 : KState := ⟨⟨362491968992467615, 362492030458308767⟩, ⟨(-421899235786850208), (-419218986272664564)⟩, true⟩

def words05 : List Nat := [371285536062768664, 371285536016683162, 371285536161114463, 371285536291043908, 371285536493053444, 371285536695877748, 371285536895410319, 371285536897617504, 371285536976836127, 371285537080166039]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 64550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 64500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485374826358394, 362485436311786762⟩, ⟨3823356815555090, 6504870983042300⟩, true⟩

def words06 : List Nat := [371285537238944168, 371285537241145611, 371285537152660449, 371285537064421634, 371285536975365425, 371285536924115430, 371285536866529285, 371285536959344734, 371285537050878619, 371285537053167946]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 64560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 64500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362509140789351039, 362509202294586374⟩, ⟨(-1530890413861754003), (-1528207620656513489)⟩, true⟩

def words07 : List Nat := [371285537209464965, 371285537368424392, 371285537725422944, 371285537794282154, 371285537796031222, 371285537786594319, 371285538004113688, 371285538133249530, 371285538501171968, 371285538870039580]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 64570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 64500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488042618787823, 362488104143879738⟩, ⟨(-168294244977485496), (-165610169337209272)⟩, true⟩

def words08 : List Nat := [371285539184056422, 371285539301153711, 371285539510933120, 371285539721902289, 371285540004674594, 371285540009127339, 371285540012599371, 371285540016793401, 371285540119553493, 371285540161756266]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 64580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 64500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476060076823879, 362476121621732095⟩, ⟨605804053525300064, 608489409200571438⟩, true⟩

def words09 : List Nat := [371285540442567873, 371285540724309664, 371285541005304642, 371285541007502497, 371285541002113174, 371285541037795374, 371285541230221355, 371285541232419380, 371285541105740297, 371285540962431795]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 64590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 64500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 64500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk645B
