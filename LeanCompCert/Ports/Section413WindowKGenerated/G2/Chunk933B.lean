import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk933A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk933B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk933A

def state06 : KState := ⟨⟨360586061220596283, 360586118676861672⟩, ⟨(-383207560464012058), (-379585367267825398)⟩, true⟩

def words05 : List Nat := [360582051295899669, 360582051535465380, 360582051772165228, 360582052066517937, 360582052331584142, 360582052596865210, 360582052758713994, 360582052806244677, 360582052850906389, 360582052895997416]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587857952269115, 360587915421264981⟩, ⟨(-550987264154225690), (-547363882380027306)⟩, true⟩

def words06 : List Nat := [360582053028628905, 360582053047081113, 360582053048284872, 360582053009068077, 360582052969628135, 360582052889416114, 360582052982002220, 360582053074854463, 360582053109890828, 360582053174074954]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591818995888619, 360591876477655105⟩, ⟨(-920844790641046247), (-917220216412916673)⟩, true⟩

def words07 : List Nat := [360582053352608840, 360582053531537044, 360582053707475938, 360582053769244223, 360582053770503892, 360582053735740353, 360582053779248432, 360582053921696688, 360582054027990836, 360582054134604454]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581350682727742, 360581408177357383⟩, ⟨56640686230378627, 60266461684045845⟩, true⟩

def words08 : List Nat := [360582054161490222, 360582054162841780, 360582054101135409, 360582054128557290, 360582054129690769, 360582054103071279, 360582053998401395, 360582053805672969, 360582053612689220, 360582053497645252]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360584059968290045, 360584117475639239⟩, ⟨(-196368902125654805), (-192741938729450859)⟩, true⟩

def words09 : List Nat := [360582053566017089, 360582053641562627, 360582053659474620, 360582053682635565, 360582053683766723, 360582053678137267, 360582053742882948, 360582053832751482, 360582053856050417, 360582053879545735]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk933B
