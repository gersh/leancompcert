import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk881A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk881B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk881A

def state06 : KState := ⟨⟨360584928827964312, 360584979834121974⟩, ⟨(-249947086569451997), (-246910478667223303)⟩, true⟩

def words05 : List Nat := [360582180258874780, 360582180110483345, 360582179961727153, 360582179851644354, 360582179722058293, 360582179484591638, 360582179246886988, 360582179120290396, 360582179124106966, 360582179157193772]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 88150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 88100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585974899323647, 360586025917569294⟩, ⟨(-342269189785567797), (-339231516146694371)⟩, true⟩

def words06 : List Nat := [360582179158325168, 360582179126958067, 360582179081881167, 360582179112257820, 360582179113346535, 360582179022616209, 360582178894691580, 360582178702521842, 360582178510112860, 360582178490227576]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 88160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 88100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560835078707648, 360560886108934391⟩, ⟨1874484875255872576, 1877523605326558518⟩, true⟩

def words07 : List Nat := [360582178610143018, 360582178730321475, 360582178765142647, 360582178766412856, 360582178672644756, 360582178545803059, 360582178418773502, 360582178420043723, 360582178292893795, 360582178052746215]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 88170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 88100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588424891511556, 360588475933721561⟩, ⟨(-558488400315191082), (-555448613500211670)⟩, true⟩

def words08 : List Nat := [360582177812315911, 360582177676419465, 360582177684743602, 360582177740215691, 360582177741387436, 360582177687772534, 360582177637266644, 360582177607038751, 360582177614983639, 360582177687715731]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 88180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 88100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585045077460448, 360585096131806853⟩, ⟨(-260468379868631677), (-257427522687375859)⟩, true⟩

def words09 : List Nat := [360582177688858831, 360582177678161064, 360582177667232021, 360582177645551758, 360582177646615886, 360582177613038675, 360582177579320199, 360582177481419998, 360582177450920423, 360582177485502533]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 88190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 88100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 88100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk881B
