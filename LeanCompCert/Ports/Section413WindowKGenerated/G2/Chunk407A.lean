import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk407A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360606617850037748, 360606628067780665⟩, ⟨(-979819488977761651), (-979538426512816697)⟩, true⟩

def state01 : KState := ⟨⟨360570541485975938, 360570551708970625⟩, ⟨488396530921910170, 488677807160382652⟩, true⟩

def words00 : List Nat := [360582561665208241, 360582561665760725, 360582561565204891, 360582561394527638, 360582561223720606, 360582560637731048, 360582559450887213, 360582557961661889, 360582556472404144, 360582555585344008]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360486822537487271, 360486832765694168⟩, ⟨3897099674288955983, 3897381162742395083⟩, true⟩

def words01 : List Nat := [360582555290937971, 360582555088523227, 360582554886048897, 360582554294594732, 360582553102465151, 360582551553399879, 360582550004240361, 360582548719296023, 360582546833806227, 360582544483836172]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360551654775515516, 360551665008935996⟩, ⟨1256869447499499243, 1257151148276437281⟩, true⟩

def words02 : List Nat := [360582542133856787, 360582540161300255, 360582538649380699, 360582537611580997, 360582536573794454, 360582535030766099, 360582533501595655, 360582532451808173, 360582531401912606, 360582530492566648]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360514271325653944, 360514281564344773⟩, ⟨2779623101740878603, 2779905017204608255⟩, true⟩

def words03 : List Nat := [360582529735270561, 360582528676018881, 360582527616723465, 360582526144335651, 360582525019482655, 360582523741070055, 360582522462658968, 360582520787085776, 360582518511522979, 360582516837226575]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360504048068327136, 360504058312221762⟩, ⟨3196219297369792322, 3196501424862367074⟩, true⟩

def words04 : List Nat := [360582515162818578, 360582513945949994, 360582512556815236, 360582510861570734, 360582509166316101, 360582507202181672, 360582505539195231, 360582503861466320, 360582502183760799, 360582500064979121]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk407A
