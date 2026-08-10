import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk724A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487209656154335, 362487287652525241⟩, ⟨(-149691439984655291), (-145877848734773045)⟩, true⟩

def state01 : KState := ⟨⟨362491169040272290, 362491247058920569⟩, ⟨(-436348905076004336), (-432533700830149724)⟩, true⟩

def words00 : List Nat := [371285272902650689, 371285272947216436, 371285273112461282, 371285273278689556, 371285273415688137, 371285273418174397, 371285273409036890, 371285273488191428, 371285273659003327, 371285273744081247]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 72400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 72400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481831612152307, 362481909653401255⟩, ⟨239826686722650856, 243643527595005958⟩, true⟩

def words01 : List Nat := [371285273829134010, 371285273915002208, 371285274050087084, 371285274092625715, 371285274141993154, 371285274192318411, 371285274226764707, 371285274229250366, 371285274009523553, 371285273966126953]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 72410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 72400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476882694889142, 362476960758298837⟩, ⟨598320400341765553, 602138846212655589⟩, true⟩

def words02 : List Nat := [371285274065327868, 371285274067857837, 371285274058328820, 371285274048910758, 371285274085801454, 371285274088540803, 371285274088339489, 371285274137434944, 371285274145842865, 371285274148416367]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 72420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 72400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495726568233877, 362495804654145363⟩, ⟨(-766622291016516111), (-762802215226397895)⟩, true⟩

def words03 : List Nat := [371285274110942429, 371285274189593716, 371285274444066815, 371285274446553050, 371285274447376373, 371285274394469007, 371285274406589273, 371285274409329217, 371285274526878320, 371285274675055809]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 72430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 72400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485341359682147, 362485419468092059⟩, ⟨(-14314588646973896), (-10492882961191184)⟩, true⟩

def words04 : List Nat := [371285274821588118, 371285274824076925, 371285274768561263, 371285274776196010, 371285274840368345, 371285274842873543, 371285274767942967, 371285274683185439, 371285274635868991, 371285274640788624]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 72440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 72400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk724A
