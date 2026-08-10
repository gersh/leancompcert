import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk556A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360551232321190613, 360551251882665143⟩, ⟨1701583477380942304, 1702318315304326724⟩, true⟩

def state01 : KState := ⟨⟨360565000938489187, 360565020507275487⟩, ⟨935902294357899594, 936637538852088000⟩, true⟩

def words00 : List Nat := [360581868568531658, 360581867858826424, 360581867311318466, 360581867086503376, 360581866861640927, 360581866313544445, 360581865442865957, 360581864680124174, 360581863917168233, 360581863476864628]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 55600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 55600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360552362690322212, 360552382266482142⟩, ⟨1638759383487525182, 1639495038064781296⟩, true⟩

def words01 : List Nat := [360581863174689527, 360581862655960348, 360581862137103014, 360581861762152895, 360581861630655613, 360581861262465391, 360581860894198671, 360581860364965047, 360581859513259016, 360581858984174785]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 55610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 55600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360556682160868659, 360556701744324963⟩, ⟨1398596498141447887, 1399332558579826265⟩, true⟩

def words02 : List Nat := [360581858454843810, 360581858248008056, 360581858160838282, 360581857912745776, 360581857664534660, 360581857303380519, 360581857126848068, 360581856842038801, 360581856557173731, 360581856023645111]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 55620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 55600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360589588821117013, 360589608411879349⟩, ⟨(-432186420253839988), (-431449953344840150)⟩, true⟩

def words03 : List Nat := [360581855572107854, 360581855443026553, 360581855505993353, 360581855506767386, 360581855377548263, 360581854972907596, 360581854568121089, 360581854141272575, 360581854098469247, 360581854238637588]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 55630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 55600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360549644243549899, 360549663841692012⟩, ⟨1790386793087751899, 1791123670642775827⟩, true⟩

def words04 : List Nat := [360581854239329064, 360581854155143572, 360581853869396673, 360581853576387090, 360581853283183456, 360581852850172270, 360581852095039319, 360581851164258444, 360581850233366321, 360581849352395387]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 55640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 55600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk556A
