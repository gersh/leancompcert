import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk588A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk588B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk588A

def state06 : KState := ⟨⟨362487346444660310, 362487397164274850⟩, ⟨(-140288630264588915), (-138272037758920635)⟩, true⟩

def words05 : List Nat := [371285047201812181, 371285047201720449, 371285047451278846, 371285047584693846, 371285047784283910, 371285047984683888, 371285048160716541, 371285048162705661, 371285047993651510, 371285048036027642]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 58850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 58800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476490049437939, 362476540786791392⟩, ⟨498762482312805511, 500780119023447785⟩, true⟩

def words06 : List Nat := [371285048224580815, 371285048226574328, 371285048117460065, 371285047956259363, 371285047794266647, 371285047705519124, 371285047472200250, 371285047424443641, 371285047376050360, 371285047328646725]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 58860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 58800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486890516256699, 362486941271608348⟩, ⟨(-113554013834088653), (-111535317480596595)⟩, true⟩

def words07 : List Nat := [371285047220987202, 371285047258881621, 371285047562531315, 371285047564520815, 371285047483723298, 371285047351791769, 371285047219102897, 371285047159543111, 371285046987454709, 371285047021893150]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 58870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 58800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468075175894106, 362468125949188435⟩, ⟨994306265081375873, 996326017992120477⟩, true⟩

def words08 : List Nat := [371285047048533336, 371285047050523454, 371285046732406564, 371285046513437144, 371285046293472604, 371285046160205157, 371285045641979470, 371285045123251469, 371285044603708342, 371285044373674632]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 58880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 58800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362464595329793054, 362464646121013801⟩, ⟨1199266997091508992, 1201287805778787248⟩, true⟩

def words09 : List Nat := [371285044087765003, 371285043894143286, 371285043699874674, 371285043491096466, 371285043024384640, 371285042644794880, 371285042264137793, 371285042172678901, 371285041843771085, 371285041499719723]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 58890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 58800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 58800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk588B
