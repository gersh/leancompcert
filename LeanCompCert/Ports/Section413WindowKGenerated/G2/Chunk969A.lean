import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk969A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587084789505972, 360587146864310976⟩, ⟨(-467492824430730098), (-463431215431027122)⟩, true⟩

def state01 : KState := ⟨⟨360589806361322487, 360589868449382500⟩, ⟨(-731299853546430953), (-727236960069604831)⟩, true⟩

def words00 : List Nat := [360582364372136297, 360582364373549139, 360582364372447715, 360582364294319877, 360582364215964223, 360582364110804057, 360582364126623437, 360582364188652250, 360582364196961633, 360582364275861748]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 96900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 96900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607295417130421, 360607357518453986⟩, ⟨(-2426245879442506497), (-2422181700528697801)⟩, true⟩

def words01 : List Nat := [360582364460937915, 360582364646437909, 360582364923629532, 360582365128952001, 360582365236765960, 360582365344658056, 360582365488435884, 360582365701038681, 360582365960038258, 360582366219349265]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 96910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 96900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360600386640399748, 360600448755148219⟩, ⟨(-1756629818216223945), (-1752564338097150655)⟩, true⟩

def words02 : List Nat := [360582366395549608, 360582366621702263, 360582366929458505, 360582367237622185, 360582367518562812, 360582367693643401, 360582367815053571, 360582367936621566, 360582368031995002, 360582368220148094]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 96920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 96900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590485699752032, 360590547827742125⟩, ⟨(-796825730759898695), (-792758967063598747)⟩, true⟩

def words03 : List Nat := [360582368514270841, 360582368808666756, 360582369043694390, 360582369242391536, 360582369413684448, 360582369585373951, 360582369770436974, 360582369909350738, 360582369994976296, 360582370080792294]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 96930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 96900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594272274883047, 360594334416169068⟩, ⟨(-1163962941285418915), (-1159894888617261549)⟩, true⟩

def words04 : List Nat := [360582370197482321, 360582370375591750, 360582370498291102, 360582370621230161, 360582370646103526, 360582370647510461, 360582370566184285, 360582370542548914, 360582370568490206, 360582370693374902]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 96940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 96900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk969A
