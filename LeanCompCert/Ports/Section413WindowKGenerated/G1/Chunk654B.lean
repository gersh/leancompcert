import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk654A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk654B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk654A

def state06 : KState := ⟨⟨362481461247392161, 362481524507712756⟩, ⟨257831701852347111, 260628612747728639⟩, true⟩

def words05 : List Nat := [371285506064923099, 371285506090203373, 371285506220463540, 371285506235083791, 371285506275627491, 371285506317041586, 371285506318753529, 371285506315839379, 371285506060037543, 371285506001949660]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 65450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 65400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362467252661564723, 362467315941738767⟩, ⟨1188009109770077176, 1190807320376272644⟩, true⟩

def words06 : List Nat := [371285505996199496, 371285505998429809, 371285505774280051, 371285505550836728, 371285505326483453, 371285505174431257, 371285504905160170, 371285504784678116, 371285504663455956, 371285504536826232]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 65460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 65400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488711737528995, 362488775037912092⟩, ⟨(-217058866208319806), (-214259332416005506)⟩, true⟩

def words07 : List Nat := [371285504260554662, 371285504069447874, 371285503895985574, 371285503898220762, 371285503678463647, 371285503404340613, 371285503129339739, 371285503033015036, 371285502901415374, 371285502953911909]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 65470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 65400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469599169444030, 362469662489941904⟩, ⟨1034477595134768307, 1037278446144188511⟩, true⟩

def words08 : List Nat := [371285502992802996, 371285502995035718, 371285502781759070, 371285502689589322, 371285502596339627, 371285502514370162, 371285502144493389, 371285501772662407, 371285501399906927, 371285501220223538]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 65480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 65400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470061081496526, 362470124422083557⟩, ⟨1004310401764983765, 1007112568517044401⟩, true⟩

def words09 : List Nat := [371285500979891478, 371285500949422410, 371285500918199062, 371285500878562223, 371285500698121606, 371285500590100337, 371285500603120745, 371285500605352271, 371285500418747935, 371285500186488398]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 65490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 65400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 65400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk654B
