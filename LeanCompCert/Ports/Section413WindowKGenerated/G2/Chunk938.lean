import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk938

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580358047690190, 360580416067944067⟩, ⟨150978013952822071, 154652985264198779⟩, true⟩

def state01 : KState := ⟨⟨360577992506773685, 360578050539955728⟩, ⟨372756404223163342, 376432588259833828⟩, true⟩

def words00 : List Nat := [360582064804084746, 360582064730864405, 360582064544037368, 360582064407382256, 360582064270370049, 360582064089540107, 360582063918077938, 360582063658483630, 360582063398618147, 360582063252760971]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568426736761620, 360568484782721994⟩, ⟨1270244287515019452, 1273921670352990078⟩, true⟩

def words01 : List Nat := [360582063281858625, 360582063353990095, 360582063368992953, 360582063386910732, 360582063388048201, 360582063355477971, 360582063342180500, 360582063343538991, 360582063285353956, 360582063142030809]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584122142700276, 360584180201503224⟩, ⟨(-202450738960093057), (-198772151169356063)⟩, true⟩

def words02 : List Nat := [360582062998426949, 360582062808600774, 360582062688909723, 360582062608030096, 360582062527060942, 360582062348856528, 360582062098302506, 360582061961689836, 360582061824655002, 360582061795526848]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578120412175643, 360578178483903438⟩, ⟨360732108170411430, 364411908762792020⟩, true⟩

def words03 : List Nat := [360582061796736882, 360582061763717286, 360582061783462994, 360582061909786274, 360582061956249725, 360582062002913801, 360582062004124822, 360582061986869545, 360582061856091144, 360582061816264508]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569145777674427, 360569203862210125⟩, ⟨1202946455505262599, 1206627458056573971⟩, true⟩

def words04 : List Nat := [360582061775990382, 360582061709142653, 360582061644845467, 360582061524039980, 360582061403014126, 360582061244572591, 360582061142361049, 360582061074246617, 360582061006007006, 360582060840985369]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360586865197476642, 360586923294840300⟩, ⟨(-460111867350411376), (-456429660832865502)⟩, true⟩

def words05 : List Nat := [360582060705090026, 360582060683068914, 360582060727323748, 360582060728682553, 360582060706213314, 360582060587422426, 360582060468352822, 360582060388251236, 360582060416150900, 360582060469376765]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360557416862276019, 360557474972604340⟩, ⟨2303962818311301930, 2307646241753733040⟩, true⟩

def words06 : List Nat := [360582060470598595, 360582060467161381, 360582060381951041, 360582060211161474, 360582060040015080, 360582059840527741, 360582059527717163, 360582059149111039, 360582058770252619, 360582058399063845]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360546132334611415, 360546190457734711⟩, ⟨3363380333237742871, 3367064957808205721⟩, true⟩

def words07 : List Nat := [360582058138277146, 360582057991151636, 360582057843887884, 360582057615307134, 360582057427145070, 360582057208766514, 360582056990012543, 360582056768891714, 360582056464250610, 360582056083616776]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586429561474905, 360586487697424777⟩, ⟨(-419951262916505469), (-416265434123287587)⟩, true⟩

def words08 : List Nat := [360582055702682589, 360582055414484477, 360582055182445208, 360582055040856725, 360582054899149919, 360582054643485749, 360582054407467860, 360582054285217358, 360582054162556027, 360582054200773093]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586645501706619, 360586703650622588⟩, ⟨(-440239506953881477), (-436552460710165305)⟩, true⟩

def words09 : List Nat := [360582054202008644, 360582054147953560, 360582054151564412, 360582054267516087, 360582054337849676, 360582054408413017, 360582054422280924, 360582054477465276, 360582054528082300, 360582054579146138]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk938
