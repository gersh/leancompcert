import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk759A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk759A
