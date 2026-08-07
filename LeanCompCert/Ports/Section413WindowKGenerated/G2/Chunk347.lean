import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk347

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

def state06 : KState := ⟨⟨360668268471295793, 360668275828773191⟩, ⟨(-3005857989390850266), (-3005685084717584666)⟩, true⟩

def words05 : List Nat := [360581795054950989, 360581796711874696, 360581798747525215, 360581799958776198, 360581800372687974, 360581800786605183, 360581802027519897, 360581803688761245, 360581806176828876, 360581808664861981]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 34750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 34700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360659287009570241, 360659294371485419⟩, ⟨(-2693641201054450626), (-2693468142101978468)⟩, true⟩

def words06 : List Nat := [360581810735344824, 360581813185839470, 360581816462978256, 360581819740064925, 360581822520246810, 360581824476369641, 360581826019355488, 360581827562300048, 360581829080700121, 360581831309102917]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 34760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 34700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360568262400905357, 360568269767208478⟩, ⟨471752356157336033, 471925567700031715⟩, true⟩

def words07 : List Nat := [360581833355490552, 360581835401846919, 360581836944792303, 360581837664065218, 360581837909958938, 360581838155974426, 360581839006834028, 360581839034193587, 360581839034608674, 360581838644945685]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 34770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 34700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360619837320100350, 360619844690809741⟩, ⟨(-1322255907057047161), (-1322082542243184341)⟩, true⟩

def words08 : List Nat := [360581838691164762, 360581839855618895, 360581840995813939, 360581842136026261, 360581842569795834, 360581842570262037, 360581842299043670, 360581842417843050, 360581842892611335, 360581843985390432]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 34780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 34700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569624019485650, 360569631394630641⟩, ⟨425005373394009882, 425178892544666636⟩, true⟩

def words09 : List Nat := [360581844661576551, 360581845337774886, 360581846131581466, 360581847344360602, 360581848348197903, 360581849352053735, 360581849724870293, 360581849725336688, 360581849529462480, 360581849178899166]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 34790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 34700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 34700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk347
