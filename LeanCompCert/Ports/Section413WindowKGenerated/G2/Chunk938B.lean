import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk938A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk938B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk938A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk938B
