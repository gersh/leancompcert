import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk682A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473739038650884, 362473807926291934⟩, ⟨790745669103251768, 793918711098310162⟩, true⟩

def state01 : KState := ⟨⟨362488787924841114, 362488856833371116⟩, ⟨(-235669868954455871), (-232495402229932143)⟩, true⟩

def words00 : List Nat := [371285448794033006, 371285448716162497, 371285448545327925, 371285448561672159, 371285448563475758, 371285448545319055, 371285448271135017, 371285448212982476, 371285448307243196, 371285448359631838]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 68200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 68200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493062638150518, 362493131567881701⟩, ⟨(-527269830081125761), (-524093917114128291)⟩, true⟩

def words01 : List Nat := [371285448375358586, 371285448391813876, 371285448622044437, 371285448745852242, 371285448877493253, 371285449010015427, 371285449141895885, 371285449144230732, 371285449156358358, 371285449271856810]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 68210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 68200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494480173390515, 362494549123926082⟩, ⟨(-623933891267843533), (-620756558920080113)⟩, true⟩

def words02 : List Nat := [371285449522529257, 371285449654786573, 371285449786582738, 371285449919209192, 371285450116915546, 371285450218308843, 371285450533328805, 371285450849268492, 371285451121234897, 371285451256989938]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 68220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 68200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362508281160174618, 362508350131811056⟩, ⟨(-1565658400793157924), (-1562479628624633870)⟩, true⟩

def words03 : List Nat := [371285451552965646, 371285451850160300, 371285452256480123, 371285452403908051, 371285452516649927, 371285452630137326, 371285452839197016, 371285452962780389, 371285453299901020, 371285453638081119]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 68230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 68200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491137914095445, 362491206906796580⟩, ⟨(-395789800982456168), (-392609591254407378)⟩, true⟩

def words04 : List Nat := [371285453955932304, 371285454008179427, 371285454149806774, 371285454292605189, 371285454499541238, 371285454501873582, 371285454422859713, 371285454344385387, 371285454382590407, 371285454469597794]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 68240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 68200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk682A
