import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk621A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360611915241649297, 360611939860505230⟩, ⟨(-1819878550443061109), (-1818845761232395473)⟩, true⟩

def state01 : KState := ⟨⟨360598395229657628, 360598419856713176⟩, ⟨(-980315343760873117), (-979282045311952901)⟩, true⟩

def words00 : List Nat := [360582651774595706, 360582651940658094, 360582651953142781, 360582651965737427, 360582651966466514, 360582652058635814, 360582652413564662, 360582652768649018, 360582652957641746, 360582653212393942]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 62100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 62100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360619755594269431, 360619780229564138⟩, ⟨(-2307231055879075022), (-2306197245656750730)⟩, true⟩

def words01 : List Nat := [360582653382908934, 360582653553660227, 360582653929384261, 360582654228640516, 360582654278027175, 360582654327480128, 360582654415536244, 360582654755144710, 360582655353490506, 360582655952014570]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 62110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 62100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589301982182228, 360589326625773145⟩, ⟨(-415457676074760802), (-414423350452032528)⟩, true⟩

def words02 : List Nat := [360582656420016712, 360582656702801537, 360582656981281088, 360582657260006632, 360582657344721614, 360582657345593211, 360582657172363955, 360582656816668567, 360582656460811831, 360582656471575530]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 62120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 62100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558966224670858, 360558990876481503⟩, ⟨1469566244966422970, 1470601081321765546⟩, true⟩

def words03 : List Nat := [360582656838585885, 360582657205766883, 360582657424771281, 360582657469162583, 360582657469894297, 360582657334938208, 360582657322720802, 360582657323592537, 360582657189505234, 360582656809557168]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 62130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 62100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360617371667355854, 360617396327390236⟩, ⟨(-2160024433189549787), (-2158989085770073429)⟩, true⟩

def words04 : List Nat := [360582656429419483, 360582656315064471, 360582656581275407, 360582656847644838, 360582656891335689, 360582657026865013, 360582657302644966, 360582657578671239, 360582657966291214, 360582658526135710]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 62140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 62100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk621A
