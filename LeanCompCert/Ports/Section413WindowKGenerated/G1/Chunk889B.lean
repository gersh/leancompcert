import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk889A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk889B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk889A

def state06 : KState := ⟨⟨362481303862268797, 362481423506452737⟩, ⟨324824540289124048, 332010967752186370⟩, true⟩

def words05 : List Nat := [371285155286536483, 371285155432309193, 371285155575590490, 371285155578691441, 371285155594463410, 371285155624337175, 371285155717247613, 371285155720355051, 371285155682553022, 371285155644129808]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486527714299865, 362486647386258634⟩, ⟨(-139928425041667995), (-132739526589087575)⟩, true⟩

def words06 : List Nat := [371285155642352252, 371285155645769622, 371285155637788825, 371285155656024432, 371285155658448834, 371285155659526605, 371285155491289585, 371285155428844607, 371285155424725847, 371285155444765462]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485870718453366, 362485990418629070⟩, ⟨(-81443919216349882), (-74252510158538922)⟩, true⟩

def words07 : List Nat := [371285155458209700, 371285155472692450, 371285155605855023, 371285155676920197, 371285155784756725, 371285155893818530, 371285155970138526, 371285155973248645, 371285155929429117, 371285155942615556]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477629369387201, 362477749097167753⟩, ⟨651919126619305380, 659112992100991906⟩, true⟩

def words08 : List Nat := [371285156061948910, 371285156065050738, 371285156016366576, 371285155969456063, 371285155921281631, 371285155885772663, 371285155785909432, 371285155755450329, 371285155723971953, 371285155693325760]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493219091541699, 362493338847441249⟩, ⟨(-735516331741944086), (-728319963816205778)⟩, true⟩

def words09 : List Nat := [371285155612237444, 371285155585272177, 371285155651971702, 371285155655073901, 371285155584629961, 371285155479532197, 371285155390862847, 371285155394358340, 371285155473542195, 371285155569008241]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk889B
