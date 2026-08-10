import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk863A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk863B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk863A

def state06 : KState := ⟨⟨360588920361143434, 360588969227822572⟩, ⟨(-586237925433423865), (-583388015406569659)⟩, true⟩

def words05 : List Nat := [360582213531973078, 360582213573193935, 360582213748007381, 360582213788939057, 360582213790097724, 360582213715308738, 360582213698228908, 360582213843723817, 360582213922973751, 360582214002484670]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 86350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 86300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594287281848549, 360594336160345572⟩, ⟨(-1049876339842938930), (-1047025409163579654)⟩, true⟩

def words06 : List Nat := [360582214003598605, 360582213980931872, 360582213887487569, 360582213889411968, 360582213890452846, 360582213821076180, 360582213782951207, 360582213677833647, 360582213600063616, 360582213741835151]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 86360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 86300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360575540949112206, 360575589839326106⟩, ⟨569410749800594861, 572262692525065309⟩, true⟩

def words07 : List Nat := [360582214017125206, 360582214292661471, 360582214465390931, 360582214580435453, 360582214660472889, 360582214740837214, 360582214866303183, 360582214867545343, 360582214859059033, 360582214783671152]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 86370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 86300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588260510026841, 360588309411958153⟩, ⟨(-529355085985271459), (-526502131052935599)⟩, true⟩

def words08 : List Nat := [360582214765189690, 360582214890983620, 360582215037137300, 360582215183518926, 360582215214758410, 360582215216001120, 360582215157973405, 360582215038142727, 360582214930627085, 360582215002458866]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 86380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 86300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360594285469196071, 360594334382977301⟩, ⟨(-1049913191914349605), (-1047059213210604305)⟩, true⟩

def words09 : List Nat := [360582215003577009, 360582214989831520, 360582215019890120, 360582215202908513, 360582215324342626, 360582215445976140, 360582215491716674, 360582215499380820, 360582215640649941, 360582215782345242]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 86390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 86300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 86300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk863B
