import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk991A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360560284652126273, 360560349690228459⟩, ⟨2183629110419243869, 2187981135355298911⟩, true⟩

def state01 : KState := ⟨⟨360595547802410555, 360595612854105514⟩, ⟨(-1311145555987827353), (-1306792183940922989)⟩, true⟩

def words00 : List Nat := [360582427986620353, 360582427848914767, 360582427779543857, 360582427796595667, 360582427797923992, 360582427728598536, 360582427661106810, 360582427601452432, 360582427581850562, 360582427716391831]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360585999261754082, 360586064327172740⟩, ⟨(-364758957546860298), (-360404225274781806)⟩, true⟩

def words01 : List Nat := [360582427799719316, 360582427883209402, 360582427964013913, 360582428096030280, 360582428184947884, 360582428274098594, 360582428311853293, 360582428313293919, 360582428286100798, 360582428324456114]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569055148860127, 360569120227843356⟩, ⟨1314796570016329562, 1319152646876324038⟩, true⟩

def words02 : List Nat := [360582428377998807, 360582428379440751, 360582428377700771, 360582428297721157, 360582428217515521, 360582428074877395, 360582427983060010, 360582427849927582, 360582427716640575, 360582427527821933]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360611226473262247, 360611291565839988⟩, ⟨(-2865878123672043826), (-2861520699121517748)⟩, true⟩

def words03 : List Nat := [360582427394746960, 360582427363807781, 360582427401595738, 360582427503346754, 360582427517852909, 360582427532458461, 360582427648478305, 360582427839531797, 360582428131837447, 360582428424464357]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602724506429171, 360602789612746272⟩, ⟨(-2023057838718121012), (-2018699051980719192)⟩, true⟩

def words04 : List Nat := [360582428638476024, 360582428808586928, 360582428994117904, 360582429180081492, 360582429325836597, 360582429397315377, 360582429417681880, 360582429438230621, 360582429560147394, 360582429767137245]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk991A
