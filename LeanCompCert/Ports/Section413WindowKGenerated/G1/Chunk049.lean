import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk049

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362159880383311886, 362159880665623740⟩, ⟨1577311972278523095, 1577312909886671259⟩, true⟩

def state01 : KState := ⟨⟨362342071004879906, 362342071288395398⟩, ⟨684088270720917448, 684089214233195206⟩, true⟩

def words00 : List Nat := [371281715578975705, 371281669742314881, 371281609517672671, 371281590447179987, 371281571384421641, 371281546931537692, 371281486227384683, 371281442784738527, 371281399359724172, 371281396993941874]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 4900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 4900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362362136069722184, 362362136354467845⟩, ⟨585785284091024743, 585786233649633615⟩, true⟩

def words01 : List Nat := [371281368623913541, 371281340790472379, 371281312968306162, 371281311520341897, 371281298907459193, 371281298617349507, 371281298327314750, 371281287907055910, 371281222801474380, 371281198597079560]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 4910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 4900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362195855902489108, 362195856188441454⟩, ⟨1404433119900095784, 1404434075401785364⟩, true⟩

def words02 : List Nat := [371281174402448139, 371281156585349937, 371281096672488016, 371281035653766183, 371280974659773664, 371280926624835592, 371280857930293147, 371280815815765379, 371280773718275924, 371280731254445873]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 4920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 4900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484527758387331, 362484528045562480⟩, ⟨(-19736893326889869), (-19735931790492985)⟩, true⟩

def words03 : List Nat := [371280673482267622, 371280656446675064, 371280663092719268, 371280663092854739, 371280632382711802, 371280592118543385, 371280552266403881, 371280552266553086, 371280532917517967, 371280533726236333]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 4930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 4900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362252120664434277, 362252120952838078⟩, ⟨1129606541035182793, 1129607508647383013⟩, true⟩

def words04 : List Nat := [371280533726339137, 371280532241114672, 371280502900657308, 371280508509466025, 371280517456655052, 371280517456790970, 371280472273718828, 371280418498313191, 371280364744587589, 371280324489938560]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 4940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 4900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362208880789690518, 362208881079320498⟩, ⟨1344679210559289755, 1344680184247375501⟩, true⟩

def words05 : List Nat := [371280278397618164, 371280272771228060, 371280267147063906, 371280260040904054, 371280198959307689, 371280149961701189, 371280100983793031, 371280092378264520, 371280040624285369, 371279985955176824]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 4950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 4900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362356890181915434, 362356890472768311⟩, ⟨609328612486349152, 609329592246312722⟩, true⟩

def words06 : List Nat := [371279931308046772, 371279890147068264, 371279828702143117, 371279783927911938, 371279739171675545, 371279687342963596, 371279598238482771, 371279549401127205, 371279500583355818, 371279492000383264]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 4960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 4900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362420321042224562, 362420321334320965⟩, ⟨294206394351297041, 294207380298058163⟩, true⟩

def words07 : List Nat := [371279467337132735, 371279442894265147, 371279434184533727, 371279434184684193, 371279438241657264, 371279446769117468, 371279448657218750, 371279448657355907, 371279410986754197, 371279399121529411]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 4970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 4900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362330548966041677, 362330549259358837⟩, ⟨741826443532238039, 741827435564737453⟩, true⟩

def words08 : List Nat := [371279400852376618, 371279400852513778, 371279372324560281, 371279334717084430, 371279297124641241, 371279271398174689, 371279226543918723, 371279221641524260, 371279216741050304, 371279212072097262]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 4980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 4900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362629785529113985, 362629785823676740⟩, ⟨(-753345050607259568), (-753344052353052624)⟩, true⟩

def words09 : List Nat := [371279182286014837, 371279161444572193, 371279159650392991, 371279159650531300, 371279143930025356, 371279118778910988, 371279096515974189, 371279096516128348, 371279117013050807, 371279147140942677]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 4990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 4900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 4900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk049
