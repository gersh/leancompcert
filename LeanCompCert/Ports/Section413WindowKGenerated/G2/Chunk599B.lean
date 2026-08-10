import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk599A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk599B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk599A

def state06 : KState := ⟨⟨360636032063565095, 360636054951108026⟩, ⟨(-3230701814840668409), (-3229774699262930291)⟩, true⟩

def words05 : List Nat := [360582184247398563, 360582184844956620, 360582185662599448, 360582186317741032, 360582186704281207, 360582187090864674, 360582187755533887, 360582188562540992, 360582189461592911, 360582190360803280]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 59950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 59900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360609399409730676, 360609422305270675⟩, ⟨(-1633719588543091644), (-1632791993421416378)⟩, true⟩

def words06 : List Nat := [360582191020188876, 360582191685574221, 360582192544457103, 360582193403559429, 360582194149906945, 360582194619333252, 360582194947445936, 360582195275631820, 360582195491016810, 360582195945973325]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 59960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 59900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585898139764781, 360585921043204525⟩, ⟨(-224129902797018368), (-223201833888672230)⟩, true⟩

def words07 : List Nat := [360582196678770090, 360582197411709948, 360582198004681373, 360582198392072536, 360582198709128784, 360582199026423641, 360582199505885182, 360582199708557078, 360582199771347398, 360582199834256881]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 59970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 59900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360610184400174315, 360610207311545694⟩, ⟨(-1680997047242458921), (-1680068502556105957)⟩, true⟩

def words08 : List Nat := [360582200175001583, 360582200693119887, 360582200967536129, 360582201242087151, 360582201280097694, 360582201280937134, 360582201174628939, 360582201228406026, 360582201501317616, 360582201969035049]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 59980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 59900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602415087370459, 360602438006732812⟩, ⟨(-1214891155669101161), (-1213962131564738441)⟩, true⟩

def words09 : List Nat := [360582202296896826, 360582202624839536, 360582203045024286, 360582203692722739, 360582204167452421, 360582204642300164, 360582204905461962, 360582204965685662, 360582205303581584, 360582205641746150]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 59990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 59900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 59900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk599B
