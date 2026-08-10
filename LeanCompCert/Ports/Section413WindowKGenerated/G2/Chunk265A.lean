import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk265A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360540587188338556, 360540591367072242⟩, ⟨1115204612959186581, 1115279518178735469⟩, true⟩

def state01 : KState := ⟨⟨360604904256361842, 360604908438383679⟩, ⟨(-589374972083578816), (-589299979711890448)⟩, true⟩

def words00 : List Nat := [360582675798815840, 360582676565976059, 360582677969956136, 360582679373895895, 360582679664942671, 360582679665290775, 360582679238706127, 360582679219777393, 360582679200753324, 360582679930228126]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 26500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 26500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360593451482281096, 360593455667613751⟩, ⟨(-285604620756884529), (-285529540599058121)⟩, true⟩

def words01 : List Nat := [360582680053455960, 360582680176712358, 360582681718825527, 360582683974207592, 360582685864464483, 360582687754641356, 360582688929749849, 360582688930097790, 360582689093285409, 360582689499648778]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 26510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 26500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360577591129741123, 360577595318353695⟩, ⟨134888698429549621, 134963865587528379⟩, true⟩

def words02 : List Nat := [360582690123368252, 360582690123716280, 360582689835227586, 360582688431052326, 360582687026925949, 360582685251936374, 360582684193131959, 360582683955456132, 360582683717760585, 360582682535300078]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 26520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 26500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574530563703717, 360574534755601691⟩, ⟨215999990140223303, 216075244476156449⟩, true⟩

def words03 : List Nat := [360582683025440141, 360582683707382620, 360582684668198374, 360582684668546503, 360582684213239762, 360582682464492267, 360582680715815483, 360582678278186002, 360582676555779275, 360582676249364923]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 26530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 26500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360551086989275592, 360551091184493986⟩, ⟨837925989516649626, 838001331992544084⟩, true⟩

def words04 : List Nat := [360582675942926873, 360582674907639894, 360582673264792993, 360582671198926397, 360582669133117015, 360582666704060635, 360582663879732010, 360582660343018889, 360582656806505780, 360582654323175438]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 26540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 26500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk265A
