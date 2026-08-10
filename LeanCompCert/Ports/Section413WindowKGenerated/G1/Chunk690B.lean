import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk690A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk690B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk690A

def state06 : KState := ⟨⟨362482702791610468, 362482773496965359⟩, ⟨179371701608704610, 182669495221806522⟩, true⟩

def words05 : List Nat := [371285419472528132, 371285419287066731, 371285419108291332, 371285419110900438, 371285419035240526, 371285418968195646, 371285418900325218, 371285418832556097, 371285418616284428, 371285418580881111]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 69050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 69000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481943068302115, 362482013794712791⟩, ⟨231904431137383922, 235203678972580916⟩, true⟩

def words06 : List Nat := [371285418715146423, 371285418717549459, 371285418715389774, 371285418714414267, 371285418756339204, 371285418758968585, 371285418848939915, 371285419000283685, 371285419086591807, 371285419089036993]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 69060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 69000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501180920751258, 362501251668528890⟩, ⟨(-1096960796793854701), (-1093660073035349913)⟩, true⟩

def words07 : List Nat := [371285419114939722, 371285419191393741, 371285419475802927, 371285419481818741, 371285419483665719, 371285419456042867, 371285419575851875, 371285419644761261, 371285419875548117, 371285420107418957]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 69070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 69000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484164532314200, 362484235301434545⟩, ⟨78565800791612526, 81867999010091182⟩, true⟩

def words08 : List Nat := [371285420338733446, 371285420370533664, 371285420468209491, 371285420567085744, 371285420691177308, 371285420693540017, 371285420538690247, 371285420385072583, 371285420245847068, 371285420248590575]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 69080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 69000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362463043383019965, 362463114173358780⟩, ⟨1537984446044559396, 1541288110358465852⟩, true⟩

def words09 : List Nat := [371285420316730798, 371285420402952097, 371285420486162572, 371285420488525505, 371285420314382415, 371285420181106777, 371285420046617229, 371285420001084742, 371285419676018181, 371285419355853114]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 69090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 69000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 69000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk690B
