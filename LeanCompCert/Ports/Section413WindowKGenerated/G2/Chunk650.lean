import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk650

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581152792616506, 360581179862944124⟩, ⟨114003410155449166, 115192019676196994⟩, true⟩

def state01 : KState := ⟨⟨360569936060972061, 360569963140025095⟩, ⟨843122260561554281, 844311437277764327⟩, true⟩

def words00 : List Nat := [360582952021414234, 360582951860010032, 360582951785215371, 360582951866540704, 360582951888401588, 360582951889317180, 360582951675310347, 360582951325097795, 360582950974731607, 360582950548689574]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 65000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 65000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360561982326448730, 360562009414120308⟩, ⟨1360263128541087983, 1361452865592104823⟩, true⟩

def words01 : List Nat := [360582950386008590, 360582950423274286, 360582950424094026, 360582950313318769, 360582949966524625, 360582949560831863, 360582949154854732, 360582948924007035, 360582948721153006, 360582948400056822]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 65010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 65000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594179907867699, 360594207004195949⟩, ⟨(-733526655214197227), (-732336355263835547)⟩, true⟩

def words02 : List Nat := [360582948078769198, 360582947696955300, 360582947433269547, 360582947162644803, 360582946891968233, 360582946393529381, 360582945931173634, 360582945705102073, 360582945487696111, 360582945661832095]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 65020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 65000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360587097061335767, 360587124166382488⟩, ⟨(-272855973765420746), (-271665106808966722)⟩, true⟩

def words03 : List Nat := [360582945700415065, 360582945739102780, 360582946013585395, 360582946407441303, 360582946741908101, 360582947076514193, 360582947212353684, 360582947213270510, 360582947272551613, 360582947337815754]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 65030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 65000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593121660033396, 360593148773704042⟩, ⟨(-664731957696133577), (-663540529797126253)⟩, true⟩

def words04 : List Nat := [360582947591869549, 360582947767435713, 360582947768266064, 360582947763158615, 360582947757884600, 360582947779695924, 360582947993612338, 360582948207697313, 360582948303426414, 360582948461183142]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 65040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 65000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk650
