import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk816

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

def state06 : KState := ⟨⟨360583447578533382, 360583491081838367⟩, ⟨(-102589222687236557), (-100190015440728589)⟩, true⟩

def words05 : List Nat := [360582263098323745, 360582263336553009, 360582263525028211, 360582263798627733, 360582263968698987, 360582264138940080, 360582264218151229, 360582264219320801, 360582264163832157, 360582264180190816]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 81650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 81600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601269829116068, 360601313343455797⟩, ⟨(-1558017011836565542), (-1555616903437384794)⟩, true⟩

def words06 : List Nat := [360582264315190140, 360582264505020559, 360582264605852772, 360582264706819047, 360582264769990369, 360582264931438619, 360582265242338729, 360582265553458530, 360582265749451486, 360582265983885848]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 81660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 81600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611674905375995, 360611718430753762⟩, ⟨(-2407852354304390995), (-2405451344374693893)⟩, true⟩

def words07 : List Nat := [360582266367858074, 360582266752165000, 360582267144859627, 360582267433000148, 360582267573519711, 360582267714127365, 360582268004281001, 360582268369894461, 360582268731399052, 360582269093155365]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 81670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 81600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602274279330655, 360602317815863931⟩, ⟨(-1640125844381707331), (-1637723923215338677)⟩, true⟩

def words08 : List Nat := [360582269361874549, 360582269481189349, 360582269596586828, 360582269712320230, 360582269724946829, 360582269764318419, 360582269765360915, 360582269720847095, 360582269780190825, 360582270026961661]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 81680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 81600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360564100170055637, 360564143717602424⟩, ⟨1478593311332335137, 1480996132247184343⟩, true⟩

def words09 : List Nat := [360582270391668410, 360582270756596014, 360582271028007895, 360582271150040973, 360582271234312135, 360582271318894036, 360582271326519000, 360582271327689160, 360582271185905756, 360582270965243149]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 81690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 81600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 81600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk816
