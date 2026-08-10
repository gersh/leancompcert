import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk384A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk384B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk384A

def state06 : KState := ⟨⟨360656402131656334, 360656411213791476⟩, ⟨(-2856776951241415194), (-2856540848995065002)⟩, true⟩

def words05 : List Nat := [360582128768344949, 360582129021975797, 360582129950144677, 360582131422439224, 360582132724205129, 360582134025993459, 360582134991183227, 360582136248557711, 360582138180204132, 360582140111922179]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 38450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 38400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360621953435978726, 360621962523001384⟩, ⟨(-1531683297633616984), (-1531447007388189694)⟩, true⟩

def words06 : List Nat := [360582142717778777, 360582144651783301, 360582146246903849, 360582147841998379, 360582148943798477, 360582150387409339, 360582151590544346, 360582152793711664, 360582153658221593, 360582154693535340]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 38460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 38400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360622384288307381, 360622393380245086⟩, ⟨(-1548320243654948605), (-1548083764304406295)⟩, true⟩

def words07 : List Nat := [360582155669282844, 360582156645140150, 360582158117900371, 360582158919274711, 360582159162532881, 360582159405812719, 360582160174347419, 360582161466692535, 360582162512648597, 360582163558662893]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 38470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 38400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605495982658551, 360605505079542526⟩, ⟨(-898561878077802461), (-898325208369720793)⟩, true⟩

def words08 : List Nat := [360582164195448897, 360582164383963527, 360582164936794480, 360582165489753810, 360582165740708795, 360582166008060444, 360582166008523534, 360582165937644652, 360582165894528765, 360582166501475713]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 38480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 38400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360562717827081566, 360562726928869264⟩, ⟨748304620881621449, 748541479358128043⟩, true⟩

def words09 : List Nat := [360582167574013509, 360582168646595095, 360582169171629938, 360582169412390718, 360582169483153268, 360582169554049753, 360582170146584083, 360582170147104223, 360582170069161534, 360582169564696748]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 38490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 38400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 38400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk384B
