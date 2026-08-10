import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk936A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589233422019073, 360589291185619382⟩, ⟨(-679624261942151255), (-675973339067355883)⟩, true⟩

def state01 : KState := ⟨⟨360605743175582244, 360605800951935083⟩, ⟨(-2225057534208495826), (-2221405417632595414)⟩, true⟩

def words00 : List Nat := [360582069517742799, 360582069671450088, 360582069754154086, 360582069837027432, 360582069871505932, 360582069963297320, 360582070168780136, 360582070374518398, 360582070521958508, 360582070776874112]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602294152137748, 360602351941295389⟩, ⟨(-1902260036457877045), (-1898606721161424359)⟩, true⟩

def words01 : List Nat := [360582071000743697, 360582071224988426, 360582071434127407, 360582071529699260, 360582071530949164, 360582071528419047, 360582071616200228, 360582071795647089, 360582072013367398, 360582072231388836]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595439009089843, 360595496811141446⟩, ⟨(-1260567368010704237), (-1256912845517712711)⟩, true⟩

def words02 : List Nat := [360582072363738804, 360582072382425435, 360582072494699450, 360582072607369873, 360582072638923044, 360582072642776416, 360582072643995272, 360582072577253763, 360582072556198655, 360582072701118936]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360572949660185245, 360573007475025518⟩, ⟨845275875461730222, 848931595420021510⟩, true⟩

def words03 : List Nat := [360582072938510502, 360582073176192853, 360582073332855060, 360582073375880851, 360582073377015265, 360582073373939024, 360582073479877071, 360582073481232539, 360582073478122741, 360582073382708347]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593472756948491, 360593530584570220⟩, ⟨(-1076626039971381962), (-1072969123092782010)⟩, true⟩

def words04 : List Nat := [360582073286989317, 360582073274810023, 360582073314655537, 360582073354753266, 360582073356015058, 360582073298286983, 360582073252974623, 360582073264337601, 360582073358145539, 360582073481890134]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk936A
