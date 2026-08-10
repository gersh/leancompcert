import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk650A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk650B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk650A

def state06 : KState := ⟨⟨360614393909100347, 360614421031435397⟩, ⟨(-2048625301072463295), (-2047433309510991317)⟩, true⟩

def words05 : List Nat := [360582948613056822, 360582948765195935, 360582949152837857, 360582949504222568, 360582949654439275, 360582949804724780, 360582950121680323, 360582950621198816, 360582951105655754, 360582951590303060]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 65050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 65000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587417760062488, 360587444891126519⟩, ⟨(-293534244081894989), (-292341684569947153)⟩, true⟩

def words06 : List Nat := [360582951956377831, 360582952086989346, 360582952453150630, 360582952819569485, 360582952951102667, 360582952952019140, 360582952848047020, 360582952572809604, 360582952297405752, 360582952234112336]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 65060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 65000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360565834454014266, 360565861593724645⟩, ⟨1111069255222098941, 1112262377393670075⟩, true⟩

def words07 : List Nat := [360582952539566182, 360582952845202445, 360582953032467587, 360582953033384147, 360582952985109993, 360582952813480641, 360582952641577523, 360582952629993533, 360582952549572966, 360582952287907093]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 65070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 65000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602129007974845, 360602156156330062⟩, ⟨(-1251168326312244440), (-1249974641490494044)⟩, true⟩

def words08 : List Nat := [360582952026041703, 360582951991707351, 360582952172030789, 360582952352524072, 360582952353369382, 360582952333076471, 360582952319138666, 360582952256722632, 360582952366141991, 360582952662122100]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 65080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 65000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360595479136945509, 360595506294047230⟩, ⟨(-818380259706706182), (-817186005533370766)⟩, true⟩

def words09 : List Nat := [360582952810544395, 360582952959058291, 360582953002166476, 360582953192637521, 360582953287857403, 360582953383223870, 360582953384049152, 360582953361661656, 360582953512558505, 360582953706444377]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 65090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 65000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 65000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk650B
