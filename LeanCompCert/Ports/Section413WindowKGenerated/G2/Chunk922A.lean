import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk922A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360564944046976310, 360565000029580360⟩, ⟨1561755547426755646, 1565241012476603172⟩, true⟩

def state01 : KState := ⟨⟨360574704996398430, 360574760991589804⟩, ⟨661828640343559165, 665315266005257663⟩, true⟩

def words00 : List Nat := [360581976430181718, 360581976344995971, 360581976465569331, 360581976586419821, 360581976608699577, 360581976610032953, 360581976514807031, 360581976415757606, 360581976316320235, 360581976209744075]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 92200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 92200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360573180144709876, 360573236152609119⟩, ⟨802380280011995931, 805868077529059235⟩, true⟩

def words01 : List Nat := [360581976132705882, 360581975965235083, 360581975797519813, 360581975615792856, 360581975500731445, 360581975356527199, 360581975212180803, 360581974996082397, 360581974784963214, 360581974691727847]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 92210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 92200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582292168302622, 360582348188758590⟩, ⟨(-37986084425201832), (-34497128864464212)⟩, true⟩

def words02 : List Nat := [360581974620726394, 360581974622066435, 360581974611477871, 360581974542489304, 360581974473300299, 360581974294809402, 360581974199336588, 360581974211105187, 360581974212293500, 360581974159106256]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 92220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 92200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360598852975005571, 360598909008068432⟩, ⟨(-1565462417582222860), (-1561972299226425942)⟩, true⟩

def words03 : List Nat := [360581974257731891, 360581974356788484, 360581974572815245, 360581974698458145, 360581974709752208, 360581974721135129, 360581974849661186, 360581975037320546, 360581975222003630, 360581975406966684]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 92230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 92200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360608951014777024, 360609007060559326⟩, ⟨(-2497040860427389603), (-2493549568769448727)⟩, true⟩

def words04 : List Nat := [360581975515048583, 360581975583584736, 360581975769244180, 360581975955291525, 360581976085399419, 360581976279335367, 360581976402175987, 360581976525165886, 360581976711391503, 360581977005939112]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 92240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 92200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk922A
