import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk910A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk910B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk910A

def state06 : KState := ⟨⟨360562300663716081, 360562355217439403⟩, ⟨1784806282461276030, 1788160817442850088⟩, true⟩

def words05 : List Nat := [360581993196381026, 360581993254236417, 360581993255419395, 360581993237035509, 360581993136635824, 360581993006363630, 360581992875684881, 360581992748744522, 360581992603017185, 360581992388726938]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 91050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 91000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360562936273640800, 360562990839798035⟩, ⟨1726942617676283578, 1730298284952803988⟩, true⟩

def words06 : List Nat := [360581992174142131, 360581992031451979, 360581991948914563, 360581991864005508, 360581991779001917, 360581991593523628, 360581991287419325, 360581991034706581, 360581990781623150, 360581990491548917]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 91060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 91000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571974931690202, 360572029510386413⟩, ⟨903717317333548267, 907074126593617061⟩, true⟩

def words07 : List Nat := [360581990284108523, 360581990015569179, 360581989746783767, 360581989563919947, 360581989453837569, 360581989313248170, 360581989172538753, 360581988939174583, 360581988710503488, 360581988602685421]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 91070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 91000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575293084742660, 360575347675814495⟩, ⟨601468645595060296, 604826582089537914⟩, true⟩

def words08 : List Nat := [360581988505446180, 360581988506761971, 360581988398618787, 360581988217086590, 360581988035320768, 360581987823693268, 360581987707285866, 360581987682200358, 360581987656983856, 360581987554858183]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 91080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 91000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589944983147780, 360589999586657698⟩, ⟨(-733362064365033841), (-730002994825246093)⟩, true⟩

def words09 : List Nat := [360581987483060479, 360581987321568046, 360581987159692716, 360581987084960607, 360581986941311951, 360581986695259535, 360581986448959949, 360581986323430745, 360581986380081560, 360581986469405141]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 91090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 91000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 91000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk910B
