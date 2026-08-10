import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk340A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk340A
