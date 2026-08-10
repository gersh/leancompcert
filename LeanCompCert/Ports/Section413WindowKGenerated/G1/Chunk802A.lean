import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk802A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362467830321311955, 362467926789230400⟩, ⟨1377969970274621299, 1383194256372961081⟩, true⟩

def state01 : KState := ⟨⟨362486044746077362, 362486141238817102⟩, ⟨(-82939330706908104), (-77713053812626238)⟩, true⟩

def words00 : List Nat := [371285173387258002, 371285173223905896, 371285172981627494, 371285172881209130, 371285172779955250, 371285172654114897, 371285172426845907, 371285172356429574, 371285172366043819, 371285172381006919]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 80200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 80200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486641418184742, 362486737936175287⟩, ⟨(-130800730555650178), (-125572428165827400)⟩, true⟩

def words01 : List Nat := [371285172395188248, 371285172410300825, 371285172490062763, 371285172509809188, 371285172561851265, 371285172614980501, 371285172668114554, 371285172670893531, 371285172582073702, 371285172605050447]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 80210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 80200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473889490180047, 362473986032862245⟩, ⟨892249771632394072, 897480054913665458⟩, true⟩

def words02 : List Nat := [371285172781732067, 371285172784505315, 371285172754370400, 371285172691867952, 371285172628262911, 371285172611765341, 371285172516824761, 371285172472565525, 371285172427394143, 371285172372821284]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 80220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 80200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502600239187092, 362502696806971877⟩, ⟨(-1411336113618179767), (-1406103816231178581)⟩, true⟩

def words03 : List Nat := [371285172251107434, 371285172270283196, 371285172443246382, 371285172530084724, 371285172592409664, 371285172655565875, 371285172790787222, 371285172857009613, 371285173077284969, 371285173298837243]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 80230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 80200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483061974698017, 362483158567534188⟩, ⟨156474965250654907, 161709272888418603⟩, true⟩

def words04 : List Nat := [371285173489211193, 371285173496388346, 371285173619573568, 371285173744196637, 371285173873212032, 371285173875986180, 371285173798188162, 371285173710361289, 371285173633186279, 371285173636355228]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 80240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 80200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk802A
