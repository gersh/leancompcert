import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk759A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk759B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk759A

def state06 : KState := ⟨⟨362480154086249450, 362480240262390435⟩, ⟨373194658294176058, 377615150178403604⟩, true⟩

def words05 : List Nat := [371285211354760245, 371285211350412804, 371285211493885357, 371285211559079472, 371285211629408880, 371285211700710006, 371285211736998101, 371285211739613857, 371285211561379381, 371285211499227961]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 75950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 75900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480869287809769, 362480955487241948⟩, ⟨318881272800044014, 323303534005882066⟩, true⟩

def words06 : List Nat := [371285211503809154, 371285211506430566, 371285211397390072, 371285211289224265, 371285211180033895, 371285211124530866, 371285211061073514, 371285211117925849, 371285211158272968, 371285211160981660]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 75960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 75900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487411237233745, 362487497460317776⟩, ⟨(-178183181361430203), (-173759123205278047)⟩, true⟩

def words07 : List Nat := [371285211122820920, 371285211141988510, 371285211229100681, 371285211231717042, 371285211088219309, 371285210916798828, 371285210744306675, 371285210662483982, 371285210551330121, 371285210584346083]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 75970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 75900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475623447500849, 362475709694178187⟩, ⟨717463313447949568, 721889164344039178⟩, true⟩

def words08 : List Nat := [371285210616700676, 371285210619317292, 371285210420679518, 371285210396542431, 371285210371117631, 371285210344670344, 371285210086800688, 371285209829065451, 371285209570276339, 371285209485786873]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 75980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 75900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473480784723582, 362473567055038595⟩, ⟨880350365970887278, 884778013208983926⟩, true⟩

def words09 : List Nat := [371285209410612592, 371285209461592378, 371285209509326084, 371285209511943222, 371285209328816549, 371285209199622732, 371285209109800811, 371285209112432256, 371285209021196972, 371285208871001872]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 75990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 75900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 75900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk759B
