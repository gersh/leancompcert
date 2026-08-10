import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk750A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586980938397462, 360587017391095317⟩, ⟨(-355415863147775415), (-353569285507084485)⟩, true⟩

def state01 : KState := ⟨⟨360581520750290075, 360581557213041207⟩, ⟨54086055292268004, 55933386979397224⟩, true⟩

def words00 : List Nat := [360582303404058488, 360582303433905982, 360582303434858865, 360582303352063979, 360582303269110017, 360582303064925429, 360582302974220661, 360582303000249676, 360582303001207743, 360582302892110390]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 75000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 75000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360603107170728556, 360603143643570573⟩, ⟨(-1565198223672201486), (-1563350135019074696)⟩, true⟩

def words01 : List Nat := [360582303050575032, 360582303219312813, 360582303565187417, 360582303733698539, 360582303752254797, 360582303770884216, 360582303966772538, 360582304252422795, 360582304531086146, 360582304809977059]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 75010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 75000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599720098680923, 360599756581688224⟩, ⟨(-1311269827009795059), (-1309420975706848533)⟩, true⟩

def words02 : List Nat := [360582304963767309, 360582304964835358, 360582304941012567, 360582304907103983, 360582304872903416, 360582304793903266, 360582304778360210, 360582304665157877, 360582304614912563, 360582304848728423]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 75020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 75000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360568861587455746, 360568898080540049⟩, ⟨1004163002574809808, 1006012610004771476⟩, true⟩

def words03 : List Nat := [360582305036430502, 360582305224324533, 360582305272854844, 360582305273923114, 360582305144890097, 360582304937039662, 360582304728875165, 360582304698321333, 360582304609485854, 360582304431952693]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 75030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 75000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582957381098854, 360582993884266197⟩, ⟨(-53563312681961663), (-51712948571620401)⟩, true⟩

def words04 : List Nat := [360582304254162863, 360582304391016549, 360582304661990847, 360582304933162543, 360582305053119339, 360582305054187827, 360582305040760838, 360582304981890972, 360582304922714131, 360582304846830699]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 75040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 75000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk750A
