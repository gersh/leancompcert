import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk690

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479335373205870, 362479405951006356⟩, ⟨411975303205317782, 415264291719087610⟩, true⟩

def state01 : KState := ⟨⟨362472385463087135, 362472456061905099⟩, ⟨891558442068467006, 894848880895674066⟩, true⟩

def words00 : List Nat := [371285424310901360, 371285424313260599, 371285424157772287, 371285423924022352, 371285423689385539, 371285423491318735, 371285423227746209, 371285423154391730, 371285423080205847, 371285423006998502]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 69000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 69000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494556884186832, 362494627504339617⟩, ⟨(-638601894759362010), (-635309983509124898)⟩, true⟩

def words01 : List Nat := [371285422842411309, 371285422866947205, 371285422978795991, 371285422981171862, 371285422904863137, 371285422797117480, 371285422717246492, 371285422719846984, 371285422778625479, 371285422914671123]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 69010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 69000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475526650448847, 362475597291905880⟩, ⟨674902656165321002, 678196037942032386⟩, true⟩

def words02 : List Nat := [371285423049369344, 371285423051729656, 371285422910789318, 371285422917753033, 371285422928730171, 371285422931090536, 371285422662670017, 371285422354995360, 371285422046390341, 371285421948402216]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 69020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 69000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362470001071894425, 362470071734610244⟩, ⟨1056449287569171145, 1059744136951427213⟩, true⟩

def words03 : List Nat := [371285421874834143, 371285421944568248, 371285422013807953, 371285422016209722, 371285421910272991, 371285421869727915, 371285421884909707, 371285421887270489, 371285421666556796, 371285421446906760]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 69030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 69000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472342794942340, 362472413478823418⟩, ⟨894780438705953171, 898076749442758667⟩, true⟩

def words04 : List Nat := [371285421226208769, 371285421088695384, 371285420852377164, 371285420729857454, 371285420606626201, 371285420450062740, 371285420131277573, 371285419922162430, 371285419711733147, 371285419659119476]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 69040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 69000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk690
