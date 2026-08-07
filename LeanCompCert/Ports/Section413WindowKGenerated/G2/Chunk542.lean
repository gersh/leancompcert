import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk542

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603672102259964, 360603690652620482⟩, ⟨(-1184224127890208753), (-1183544803292564741)⟩, true⟩

def state01 : KState := ⟨⟨360582026597803122, 360582045155340929⟩, ⟨(-11095948430705875), (-10416234788959755)⟩, true⟩

def words00 : List Nat := [360581854547326492, 360581854548079495, 360581854611870240, 360581854762936630, 360581854763566967, 360581854755755859, 360581854408092791, 360581853853369591, 360581853298504601, 360581853012882960]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360532376628207984, 360532395192829916⟩, ⟨2680742911803825518, 2681423009512462662⟩, true⟩

def words01 : List Nat := [360581853175882150, 360581853339018625, 360581853339691135, 360581853266719303, 360581852853950188, 360581852206878325, 360581851559601192, 360581851251932588, 360581850604535269, 360581849693189792]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360561465453190545, 360561484024933473⟩, ⟨1103396416921592873, 1104076900764710425⟩, true⟩

def words02 : List Nat := [360581848781707570, 360581848096454903, 360581847673444841, 360581847216213663, 360581846758947937, 360581846010250918, 360581845120690955, 360581844502837116, 360581843884796044, 360581843178552590]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565935252386048, 360565953831294891⟩, ⟨860984938746137868, 861665811232509778⟩, true⟩

def words03 : List Nat := [360581842803808215, 360581842259362370, 360581841714792418, 360581841448301005, 360581841409179200, 360581841284599083, 360581841159924735, 360581840836281899, 360581840292413945, 360581840000381037]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360550719299426586, 360550737885442320⟩, ⟨1686279898460349733, 1686961156458733997⟩, true⟩

def words04 : List Nat := [360581839708113127, 360581839466887089, 360581839036235469, 360581838312748487, 360581837589166558, 360581836698773424, 360581835979087737, 360581835372935586, 360581834766726772, 360581833943625892]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360561806406023927, 360561824999144813⟩, ⟨1084777871040906070, 1085459514529924222⟩, true⟩

def words05 : List Nat := [360581833371046496, 360581833137690396, 360581832931791518, 360581832932545073, 360581832621776505, 360581832021762540, 360581831421637938, 360581830700460735, 360581830149851684, 360581829781941163]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 54250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 54200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360559642343102827, 360559660943408836⟩, ⟨1202037008516170571, 1202719041904783937⟩, true⟩

def words06 : List Nat := [360581829413941809, 360581828875153657, 360581828239016996, 360581827654121947, 360581827069030549, 360581826398568324, 360581825518679184, 360581824469327546, 360581823419870309, 360581822709428825]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 54260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 54200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360541065496933164, 360541084104345146⟩, ⟨2210281125112189353, 2210963544177952591⟩, true⟩

def words07 : List Nat := [360581822301695158, 360581821886258222, 360581821470754262, 360581820855288545, 360581820188308137, 360581819324012575, 360581818459527936, 360581817933861662, 360581817417445187, 360581816667797209]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 54270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 54200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563820690336798, 360563839304866559⟩, ⟨974928720326263727, 975611525779190743⟩, true⟩

def words08 : List Nat := [360581815918007070, 360581815142729170, 360581814548567023, 360581814105095782, 360581813661598924, 360581812871668841, 360581811742945905, 360581810953020440, 360581810162890705, 360581809677417291]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 54280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 54200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360561766319838549, 360561784941555730⟩, ⟨1086518199339812884, 1087201395034206872⟩, true⟩

def words09 : List Nat := [360581809347088245, 360581808847423432, 360581808347619387, 360581808195065534, 360581808195696795, 360581808119644145, 360581808043513790, 360581807794874169, 360581807434571807, 360581807066694482]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 54290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 54200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 54200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk542
