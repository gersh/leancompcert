import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk615

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

def state06 : KState := ⟨⟨362490244440792852, 362490300117996102⟩, ⟨(-307274609122812378), (-304959465724728486)⟩, true⟩

def words05 : List Nat := [371285346202934681, 371285346096676459, 371285346145154506, 371285346171493889, 371285346245791694, 371285346320875415, 371285346357536046, 371285346359659817, 371285346257891591, 371285346340998901]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 61550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 61500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475584676437980, 362475640372217110⟩, ⟨595290134321663218, 597606421347563268⟩, true⟩

def words06 : List Nat := [371285346686999534, 371285346689087013, 371285346683504612, 371285346677786224, 371285346678694659, 371285346680996754, 371285346572230205, 371285346548928421, 371285346524895478, 371285346502172406]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 61560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 61500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495346470977439, 362495402185631544⟩, ⟨(-621518568561772761), (-619201119307326031)⟩, true⟩

def words07 : List Nat := [371285346374920390, 371285346406408546, 371285346658688958, 371285346660782734, 371285346643503269, 371285346580637902, 371285346697178015, 371285346787663592, 371285346952397978, 371285347118008295]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 61570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 61500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490327591273196, 362490383324754323⟩, ⟨(-312457019754934056), (-310138411034699206)⟩, true⟩

def words08 : List Nat := [371285347280901364, 371285347282990585, 371285347260105192, 371285347382443325, 371285347584767494, 371285347604272293, 371285347621422606, 371285347639242491, 371285347790450910, 371285347874590587]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 61580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 61500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484578664732908, 362484634417090625⟩, ⟨41692488899436105, 44012260318692195⟩, true⟩

def words09 : List Nat := [371285348124129009, 371285348374523452, 371285348568085973, 371285348570187916, 371285348610982930, 371285348656177694, 371285348918120137, 371285348920213647, 371285348910998137, 371285348901836059]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 61590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 61500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 61500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk615
