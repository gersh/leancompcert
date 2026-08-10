import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk727A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk727B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk727A

def state06 : KState := ⟨⟨360576480266104907, 360576514491613051⟩, ⟨425998629201431934, 427680648721349434⟩, true⟩

def words05 : List Nat := [360582392651257439, 360582392728354025, 360582392729274919, 360582392712428089, 360582392668395788, 360582392576833068, 360582392506409696, 360582392534242172, 360582392535163251, 360582392455449244]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 72750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 72700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360599083320930374, 360599117556190952⟩, ⟨(-1218751084764138246), (-1217068355609706782)⟩, true⟩

def words06 : List Nat := [360582392375505175, 360582392295203899, 360582392500284190, 360582392705556701, 360582392714381740, 360582392715415342, 360582392543514861, 360582392552548197, 360582392691086713, 360582392921987634]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 72760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 72700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360574587362631850, 360574621607753153⟩, ⟨564015338671531979, 565698785438967431⟩, true⟩

def words07 : List Nat := [360582393045354563, 360582393168850225, 360582393425225367, 360582393803929055, 360582394076376974, 360582394348991387, 360582394486453917, 360582394487487692, 360582394436448527, 360582394330828710]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 72770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 72700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360568124185531284, 360568158440385891⟩, ⟨1034431791594891084, 1036115946801552812⟩, true⟩

def words08 : List Nat := [360582394257841585, 360582394258875480, 360582394149812676, 360582393945335508, 360582393740695507, 360582393488615445, 360582393380513006, 360582393211678827, 360582393042737933, 360582392757555854]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 72780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 72700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593674979352768, 360593709243987329⟩, ⟨(-825595493593675712), (-823910626455981308)⟩, true⟩

def words09 : List Nat := [360582392562841520, 360582392513481360, 360582392463822142, 360582392410473570, 360582392293831694, 360582391999374930, 360582391704728344, 360582391632933436, 360582391789231670, 360582391945784613]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 72790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 72700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 72700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk727B
