import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk759

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490976191513038, 362491062226290656⟩, ⟨(-448254179697820279), (-443844421557186667)⟩, true⟩

def state01 : KState := ⟨⟨362472972536512535, 362473058594591122⟩, ⟨918311456861500031, 922722983668537337⟩, true⟩

def words00 : List Nat := [371285214700527610, 371285214703141288, 371285214621756623, 371285214541218314, 371285214459652751, 371285214384649130, 371285214222267589, 371285214175594231, 371285214128013810, 371285214081136618]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 75900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 75900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484547021073819, 362484633102782331⟩, ⟨39615624202866883, 44028944877220031⟩, true⟩

def words01 : List Nat := [371285213922793834, 371285213823843154, 371285213794872969, 371285213797487011, 371285213639683688, 371285213437709345, 371285213234700148, 371285213184296667, 371285213046118090, 371285213041466173]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 75910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 75900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477918217690418, 362478004323011597⟩, ⟨542923193314261646, 547338306780913568⟩, true⟩

def words02 : List Nat := [371285213035781460, 371285213030774745, 371285213020755414, 371285213079211427, 371285213189350837, 371285213191965356, 371285213071064169, 371285212951034551, 371285212829951622, 371285212782207975]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 75920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 75900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362470491598808519, 362470577727650662⟩, ⟨1106917209451622355, 1111334108984205551⟩, true⟩

def words03 : List Nat := [371285212767467628, 371285212848701376, 371285212888065179, 371285212890679973, 371285212698779238, 371285212560914161, 371285212453845734, 371285212456461624, 371285212288123598, 371285212098324671]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 75930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 75900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486728704200758, 362486814856480652⟩, ⟨(-126206388841143322), (-121787709327021188)⟩, true⟩

def words04 : List Nat := [371285211907391127, 371285211890912911, 371285211787134147, 371285211727481730, 371285211666974299, 371285211577006460, 371285211358328248, 371285211301219088, 371285211328909737, 371285211352783176]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 75940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 75900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk759
