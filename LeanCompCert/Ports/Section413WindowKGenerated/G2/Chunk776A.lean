import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk776A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360606820169752442, 360606859298599213⟩, ⟨(-1917535173133140014), (-1915484384231119906)⟩, true⟩

def state01 : KState := ⟨⟨360593817211855353, 360593856351263921⟩, ⟨(-908460712000287778), (-906409103451507944)⟩, true⟩

def words00 : List Nat := [360582175775651215, 360582176071083723, 360582176486577221, 360582176902385980, 360582177170563722, 360582177273283763, 360582177291914324, 360582177310655956, 360582177325339627, 360582177477090782]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 77600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 77600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360576217848733116, 360576256998570524⟩, ⟨457573545625563282, 459625963609158428⟩, true⟩

def words01 : List Nat := [360582177794224507, 360582178111562169, 360582178324389048, 360582178411401155, 360582178412330820, 360582178404778008, 360582178553786045, 360582178561563661, 360582178562550871, 360582178487408571]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 77610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 77600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594140222450396, 360594179382761996⟩, ⟨(-933665008548675127), (-931611777508078747)⟩, true⟩

def words02 : List Nat := [360582178501458029, 360582178707840275, 360582178843757902, 360582178979865058, 360582178980900278, 360582178962181006, 360582178848271504, 360582178760947297, 360582178714616962, 360582178870369936]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 77620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 77600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591732112687293, 360591771283550132⟩, ⟨(-746710213904510413), (-744656163718707711)⟩, true⟩

def words03 : List Nat := [360582178934789754, 360582178999328616, 360582179153125964, 360582179415342230, 360582179635764633, 360582179856367266, 360582179948961384, 360582180017155422, 360582180141588994, 360582180266384992]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 77630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 77600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592473271875686, 360592512453170639⟩, ⟨(-804265635368626128), (-802210775180643430)⟩, true⟩

def words04 : List Nat := [360582180556444329, 360582180681248188, 360582180722095867, 360582180763073874, 360582180764001741, 360582180799607170, 360582181024789454, 360582181250179750, 360582181340944269, 360582181475138410]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 77640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 77600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk776A
