import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk804A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk804B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk804A

def state06 : KState := ⟨⟨360581160034181099, 360581202219733380⟩, ⟨74827472512443742, 77119860659752646⟩, true⟩

def words05 : List Nat := [360582161583067452, 360582161362528459, 360582161141774940, 360582161026995086, 360582161027958432, 360582160997503631, 360582160966928972, 360582160838172342, 360582160717277673, 360582160706691618]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360570637030780821, 360570679227167432⟩, ⟨921494175106928487, 923787435040062909⟩, true⟩

def words06 : List Nat := [360582160736256645, 360582160737407790, 360582160624828049, 360582160435216738, 360582160245447606, 360582159909463104, 360582159650437555, 360582159501489688, 360582159352429788, 360582159125701545]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585369933329638, 360585412140599666⟩, ⟨(-264111848827140912), (-261817713053738044)⟩, true⟩

def words07 : List Nat := [360582158995515075, 360582159008347162, 360582159175012016, 360582159187782610, 360582159188847244, 360582159052472779, 360582158915873687, 360582158895837878, 360582158937207901, 360582158978821685]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575879453356776, 360575921671586073⟩, ⟨499578867872814428, 501873885703562498⟩, true⟩

def words08 : List Nat := [360582158979847632, 360582158937923872, 360582158741697908, 360582158533868632, 360582158325736606, 360582158079352676, 360582157836730196, 360582157474572235, 360582157112202793, 360582156904356648]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360562916281292906, 360562958510386721⟩, ⟨1543081442870455670, 1545377335239104604⟩, true⟩

def words09 : List Nat := [360582156904487419, 360582156982301780, 360582156983345684, 360582156942526080, 360582156782400968, 360582156530750516, 360582156278749905, 360582156141969682, 360582155981626694, 360582155744364847]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk804B
