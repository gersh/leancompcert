import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk347A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360646924887872427, 360646932218933122⟩, ⟨(-2262908517061643813), (-2262736529838732223)⟩, true⟩

def state01 : KState := ⟨⟨360648790925905039, 360648798261391436⟩, ⟨(-2327945500716297831), (-2327773359899672403)⟩, true⟩

def words00 : List Nat := [360581726930077382, 360581727480642750, 360581728860732019, 360581730240882565, 360581731079383037, 360581732260529266, 360581732915176968, 360581733569837279, 360581734781749184, 360581736714334317]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 34700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 34700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360597621420172663, 360597628760044672⟩, ⟨(-551456339448412057), (-551284046385387441)⟩, true⟩

def words01 : List Nat := [360581739242328964, 360581741770267025, 360581743595384554, 360581745152388193, 360581746340444433, 360581747528558693, 360581749329924962, 360581750305083645, 360581750762826866, 360581751220619386]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 34710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 34700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360631035305427192, 360631042649687899⟩, ⟨(-1711716074934635545), (-1711543629474187411)⟩, true⟩

def words02 : List Nat := [360581752507107382, 360581754214341183, 360581756158424170, 360581758102482540, 360581759348302963, 360581760049114695, 360581760167129645, 360581760285264827, 360581761231714308, 360581762651142675]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 34720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 34700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360654006384780369, 360654013733476717⟩, ⟨(-2509715251663163426), (-2509542652130950212)⟩, true⟩

def words03 : List Nat := [360581763455264147, 360581764259386288, 360581765611794820, 360581767610719886, 360581769399329950, 360581771187915291, 360581772558434163, 360581773810513968, 360581775890335423, 360581777970196128]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 34730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 34700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360640957446385538, 360640964799471155⟩, ⟨(-2056438122226419949), (-2056265370189581887)⟩, true⟩

def words04 : List Nat := [360581780013675498, 360581781642807217, 360581782734282204, 360581783825745355, 360581784707321897, 360581786004626560, 360581788129287684, 360581790253925034, 360581791694810658, 360581793398067179]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 34740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 34700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk347A
