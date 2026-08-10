import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk615A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487847915993832, 362487903480361180⟩, ⟨(-159791625093050105), (-157483424505749551)⟩, true⟩

def state01 : KState := ⟨⟨362484731507303628, 362484787090282873⟩, ⟨31927508504657250, 34236853818320598⟩, true⟩

def words00 : List Nat := [371285342993772988, 371285342998902996, 371285343000472953, 371285342998526672, 371285343071045839, 371285343073374132, 371285343291236056, 371285343533964319, 371285343694428943, 371285343696587837]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 61500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 61500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362513572122528213, 362513627724376966⟩, ⟨(-1742200466714294542), (-1739889960640893434)⟩, true⟩

def words01 : List Nat := [371285343944414867, 371285344202398378, 371285344698152501, 371285344842315407, 371285344940071074, 371285345038488779, 371285345366901963, 371285345564498707, 371285346025636724, 371285346487715649]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 61510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 61500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482736136255963, 362482791756944534⟩, ⟨154923729561248528, 157235394758137802⟩, true⟩

def words02 : List Nat := [371285346948157432, 371285347136938369, 371285347301470845, 371285347467040203, 371285347656826059, 371285347658912192, 371285347496682504, 371285347334400976, 371285347181059724, 371285347183480503]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 61520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 61500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362471133213768249, 362471188853209030⟩, ⟨868986684408195980, 871299503525253644⟩, true⟩

def words03 : List Nat := [371285347308513077, 371285347475899836, 371285347631812459, 371285347633913081, 371285347553272030, 371285347539877397, 371285347575613674, 371285347577702226, 371285347343923995, 371285347116184741]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 61530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 61500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482039225521478, 362482094883639030⟩, ⟨197807886754421772, 200121855334977296⟩, true⟩

def words04 : List Nat := [371285346887542024, 371285346790165463, 371285346660497131, 371285346729399389, 371285346731025327, 371285346714484157, 371285346345394907, 371285346241583143, 371285346251993308, 371285346254156252]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 61540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 61500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk615A
