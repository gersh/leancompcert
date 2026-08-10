import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk641A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk641B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk641A

def state06 : KState := ⟨⟨362509801961680112, 362509862638522007⟩, ⟨(-1565199277869069536), (-1562569808609520542)⟩, true⟩

def words05 : List Nat := [371285506989395086, 371285507118097748, 371285507488681214, 371285507536172708, 371285507551201304, 371285507566851628, 371285507824688506, 371285507987376269, 371285508368448999, 371285508750512009]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 64150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 64100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485508196700399, 362485568893259089⟩, ⟨(-6401891276850296), (-3771156887889848)⟩, true⟩

def words06 : List Nat := [371285509132546520, 371285509313546728, 371285509573016155, 371285509833571053, 371285510130191620, 371285510132373731, 371285510105411569, 371285510088188030, 371285510122518139, 371285510125951616]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 64160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 64100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478606805520387, 362478667521705864⟩, ⟨436581468708167508, 439213462648687840⟩, true⟩

def words07 : List Nat := [371285510371321582, 371285510617552216, 371285510862291112, 371285510889965990, 371285510930158636, 371285510971498126, 371285511190865564, 371285511193047973, 371285511089019750, 371285510984819742]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 64170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 64100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489417549390851, 362489478285127013⟩, ⟨(-257318671680163719), (-254685422876380891)⟩, true⟩

def words08 : List Nat := [371285510932202411, 371285510934612588, 371285510929414120, 371285510967107839, 371285510968808469, 371285510931838438, 371285510606651991, 371285510525450392, 371285510602147018, 371285510666257135]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 64180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 64100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485902207691486, 362485962963334031⟩, ⟨(-31618975671980668), (-28984448978890918)⟩, true⟩

def words09 : List Nat := [371285510728976723, 371285510792469349, 371285511030023735, 371285511175642387, 371285511357056048, 371285511539295159, 371285511671536727, 371285511673719890, 371285511489438994, 371285511499198288]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 64190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 64100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 64100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk641B
