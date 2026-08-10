import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk816A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360595203660006919, 360595247096936844⟩, ⟨(-1062576217818008785), (-1060182428767706043)⟩, true⟩

def state01 : KState := ⟨⟨360588931548774604, 360588974996708410⟩, ⟨(-550784292581637098), (-548389605559140108)⟩, true⟩

def words00 : List Nat := [360582255029338331, 360582255084672217, 360582255085723260, 360582255065683549, 360582255045454175, 360582254996945203, 360582255154922257, 360582255313119394, 360582255358130923, 360582255441678339]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 81600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 81600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360613128316073900, 360613171775057769⟩, ⟨(-2525640687222989361), (-2523245098351112339)⟩, true⟩

def words01 : List Nat := [360582255674954981, 360582255908581151, 360582256108449069, 360582256319736772, 360582256402834508, 360582256486021134, 360582256619809093, 360582256849897160, 360582257229608740, 360582257609605850]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 81610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 81600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604214433658493, 360604257903776462⟩, ⟨(-1798145465915911260), (-1795748968224093240)⟩, true⟩

def words02 : List Nat := [360582257914286632, 360582258132516154, 360582258440572951, 360582258748967519, 360582259018106755, 360582259137727486, 360582259138793777, 360582259130552634, 360582259262613864, 360582259533448718]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 81620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 81600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360588098407713467, 360588141888837614⟩, ⟨(-482489527801976968), (-480092131620541416)⟩, true⟩

def words03 : List Nat := [360582259778341063, 360582260023444641, 360582260193271320, 360582260424538549, 360582260584548670, 360582260744863998, 360582261054745904, 360582261215179455, 360582261288263029, 360582261361509182]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 81630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 81600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360610070929668500, 360610114421845518⟩, ⟨(-2276506157408876809), (-2274107858816829059)⟩, true⟩

def words04 : List Nat := [360582261407651603, 360582261568101591, 360582261794910612, 360582262021936119, 360582262120928343, 360582262122097732, 360582262169453947, 360582262268923594, 360582262517890482, 360582262860213489]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 81640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 81600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk816A
