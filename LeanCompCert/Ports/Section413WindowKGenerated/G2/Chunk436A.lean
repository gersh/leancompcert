import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk436A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360557048648665799, 360557060440694334⟩, ⟨1138452580987340835, 1138800027916905315⟩, true⟩

def state01 : KState := ⟨⟨360605846617969340, 360605858415625475⟩, ⟨(-989477522079374521), (-989129829759964679)⟩, true⟩

def words00 : List Nat := [360583179108819053, 360583178957809107, 360583179045451447, 360583179133199363, 360583179133756373, 360583178736642137, 360583177815291757, 360583177419670374, 360583177153137563, 360583177673845650]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 43600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 43600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587301341409892, 360587313144730927⟩, ⟨(-180586025238581923), (-180238085844766631)⟩, true⟩

def words01 : List Nat := [360583177929552934, 360583178185313506, 360583178966345458, 360583180009988203, 360583180586620038, 360583181163317443, 360583181301389519, 360583181301985036, 360583181138416094, 360583181233820018]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 43610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 43600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360610158140772424, 360610169949701718⟩, ⟨(-1177740065191046605), (-1177391881136885517)⟩, true⟩

def words02 : List Nat := [360583181747590175, 360583182091413515, 360583182091949287, 360583182081402635, 360583182070748232, 360583182128802743, 360583182879461017, 360583183630201662, 360583184116375322, 360583184735493085]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 43620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 43600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360609228616997951, 360609240431555081⟩, ⟨(-1137270615661888282), (-1136922186036722882)⟩, true⟩

def words03 : List Nat := [360583185170290104, 360583185605239331, 360583186564873867, 360583187001162228, 360583187001711443, 360583186995498168, 360583187061894394, 360583187537721045, 360583188135199820, 360583188732784734]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 43630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 43600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577317337122860, 360577329157356271⟩, ⟨255231352479614523, 255580029845507325⟩, true⟩

def words04 : List Nat := [360583188990069083, 360583188990664839, 360583188724578039, 360583188685956989, 360583188647189439, 360583188147614526, 360583187270099114, 360583186128521812, 360583184986878397, 360583184369952961]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 43640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 43600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk436A
