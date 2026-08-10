import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk869A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk869B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk869A

def state06 : KState := ⟨⟨360604729793100316, 360604779367599144⟩, ⟨(-1968602412772940309), (-1965691162890298179)⟩, true⟩

def words05 : List Nat := [360582173956085899, 360582174010163509, 360582174164394964, 360582174322522773, 360582174345874610, 360582174369311405, 360582174431886922, 360582174561155859, 360582174822112207, 360582175083346545]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 86950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 86900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598426073040101, 360598475659473747⟩, ⟨(-1420566170037948415), (-1417653882244928261)⟩, true⟩

def words06 : List Nat := [360582175224476416, 360582175233593277, 360582175239915599, 360582175246601693, 360582175247649074, 360582175223496692, 360582175224623177, 360582175161234988, 360582175164969727, 360582175353828821]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 86960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 86900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564175671562749, 360564225269772291⟩, ⟨1558410888219963105, 1561324200221937501⟩, true⟩

def words07 : List Nat := [360582175614471372, 360582175875350386, 360582176058205328, 360582176109094559, 360582176110162025, 360582176062321091, 360582176014107596, 360582175986651892, 360582175856551944, 360582175651471785]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 86970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 86900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581584604621043, 360581634214667980⟩, ⟨44171633882871147, 47085975558062691⟩, true⟩

def words08 : List Nat := [360582175446112303, 360582175403295334, 360582175473831646, 360582175544601675, 360582175545766990, 360582175503533961, 360582175496783509, 360582175532766137, 360582175533798901, 360582175494993973]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 86980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 86900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571399746986856, 360571449368952704⟩, ⟨930247570243377800, 933162948801425212⟩, true⟩

def words09 : List Nat := [360582175489887022, 360582175412016527, 360582175386759240, 360582175509412231, 360582175578119833, 360582175647058020, 360582175648173717, 360582175641072218, 360582175501716029, 360582175379858468]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 86990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 86900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 86900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk869B
