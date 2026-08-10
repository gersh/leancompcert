import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk194A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk194B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk194A

def state06 : KState := ⟨⟨360617124878971182, 360617127071692587⟩, ⟨(-652397123404500335), (-652368244236450875)⟩, true⟩

def words05 : List Nat := [360583597612502753, 360583599778518517, 360583601767298107, 360583602166932313, 360583602167161524, 360583600308942938, 360583599218996988, 360583601800441319, 360583603523422785, 360583605246286059]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 19450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 19400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589709016425703, 360589711211515954⟩, ⟨(-119194809588706664), (-119165884311312036)⟩, true⟩

def words06 : List Nat := [360583605287633993, 360583605287883032, 360583605308056633, 360583606630894103, 360583606631103077, 360583606288131945, 360583603315866944, 360583598243471759, 360583593171550009, 360583591038730206]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 19460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 19400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360573979446595180, 360573981644028356⟩, ⟨187494121926638392, 187523092832695204⟩, true⟩

def words07 : List Nat := [360583593977128427, 360583596915272400, 360583598535869948, 360583601347553167, 360583602501369928, 360583603655135551, 360583607431049488, 360583608579881824, 360583608580103751, 360583608086165559]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 19470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 19400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360610405905432927, 360610408105220226⟩, ⟨(-522456143490467861), (-522427126714321519)⟩, true⟩

def words08 : List Nat := [360583607592227015, 360583605291545030, 360583607035513385, 360583609218041593, 360583609218273218, 360583609142742450, 360583606441665998, 360583604495885239, 360583603224166434, 360583604599668212]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 19480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 19400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360512829450657903, 360512831652818521⟩, ⟨1380047746540943732, 1380076809584522022⟩, true⟩

def words09 : List Nat := [360583604599890201, 360583604453846985, 360583605961800862, 360583609201430279, 360583610569816390, 360583611938099269, 360583611938321374, 360583611506262494, 360583608451834733, 360583604822540805]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 19490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 19400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 19400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk194B
