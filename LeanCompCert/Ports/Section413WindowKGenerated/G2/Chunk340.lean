import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk340

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360567422747169405, 360567429773578240⟩, ⟨479121667093805190, 479283189169030612⟩, true⟩

def state01 : KState := ⟨⟨360632103736788824, 360632110767491825⟩, ⟨(-1720458338768594003), (-1720296670670462307)⟩, true⟩

def words00 : List Nat := [360581525923743437, 360581525718198996, 360581526317999950, 360581526917852446, 360581526918271943, 360581526780956193, 360581527169379234, 360581527622838559, 360581528683201249, 360581530170900415]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 34000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 34000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360599695354400850, 360599702389447904⟩, ⟨(-618152311190780079), (-617990495330455545)⟩, true⟩

def words01 : List Nat := [360581531226526253, 360581532282139023, 360581533099333435, 360581534351787376, 360581535384986896, 360581536418199877, 360581536677623913, 360581536678079317, 360581536883467130, 360581537417949993]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 34010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 34000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360562502239049500, 360562509278381498⟩, ⟨647224406583657152, 647386368239512838⟩, true⟩

def words02 : List Nat := [360581538199313123, 360581538199768505, 360581538120709896, 360581537388058381, 360581536655376196, 360581535692384120, 360581535235149833, 360581534750555878, 360581534265945152, 360581533268044723]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 34020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 34000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360691402991733739, 360691410035365906⟩, ⟨(-3739923584881765691), (-3739761476870349819)⟩, true⟩

def words03 : List Nat := [360581533012716362, 360581533316522759, 360581534482436744, 360581536439417024, 360581537661132085, 360581538882811146, 360581540707535026, 360581543073777903, 360581546301730461, 360581549529597264]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 34030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 34000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360651358662395714, 360651365710372327⟩, ⟨(-2376912952372935617), (-2376750696455097175)⟩, true⟩

def words04 : List Nat := [360581552101746665, 360581553814198737, 360581556081892186, 360581558349585621, 360581560051228310, 360581561322474916, 360581561984874226, 360581562647287189, 360581563927283963, 360581565977722623]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 34040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 34000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360581039903695588, 360581046955962445⟩, ⟨17859851399079246, 18022253421385048⟩, true⟩

def words05 : List Nat := [360581568308619552, 360581570639465773, 360581572536198703, 360581573573883141, 360581573990417193, 360581574407048666, 360581575684527477, 360581576103132031, 360581576103538099, 360581576088476285]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 34050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 34000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360582263862462630, 360582270919036900⟩, ⟨(-23578911398451597), (-23416362644151553)⟩, true⟩

def words06 : List Nat := [360581576918599840, 360581578435949429, 360581580342642606, 360581582249310520, 360581583418210918, 360581583728423952, 360581583774724271, 360581583821153323, 360581583821528785, 360581583637693701]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 34060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 34000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567910888818388, 360567917949734326⟩, ⟨465428508621650927, 465591205318233009⟩, true⟩

def words07 : List Nat := [360581583638100113, 360581583118142157, 360581582598129280, 360581582492401708, 360581582492784358, 360581582198022866, 360581581903221284, 360581581044511711, 360581580063869189, 360581579663505401]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 34070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 34000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563322684785405, 360563329750004430⟩, ⟨621697528241548176, 621860371608611836⟩, true⟩

def words08 : List Nat := [360581579539913252, 360581579540369463, 360581578959900480, 360581577697170120, 360581576434440562, 360581574660458281, 360581573557380089, 360581573079193379, 360581572600987613, 360581571474017590]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 34080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 34000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360562651995738645, 360562659065262894⟩, ⟨644632966174414198, 644795956328181456⟩, true⟩

def words09 : List Nat := [360581571037220779, 360581571135645399, 360581571850921503, 360581571851377944, 360581571709388098, 360581570835265079, 360581569961112441, 360581569059849431, 360581568591644340, 360581568037589234]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 34090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 34000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 34000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk340
