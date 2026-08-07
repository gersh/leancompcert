import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk461

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492106968921110, 362492137475115009⟩, ⟨(-305970187123362427), (-305020018212365039)⟩, true⟩

def state01 : KState := ⟨⟨362476627612565358, 362476658132557704⟩, ⟨407700591466532600, 408651396555831036⟩, true⟩

def words00 : List Nat := [371285521184841774, 371285521186398257, 371285521113803315, 371285521313662224, 371285521656245129, 371285521657774280, 371285521373966870, 371285521075737547, 371285520776932401, 371285520665556096]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 46100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 46100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362453969095807815, 362453999629594428⟩, ⟨1452671688288235133, 1453623129499871243⟩, true⟩

def words01 : List Nat := [371285520591922855, 371285520711133259, 371285520808654287, 371285520810183850, 371285520281395213, 371285519806826235, 371285519331453024, 371285519275223726, 371285518592487060, 371285517910806481]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 46110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 46100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362455005508212755, 362455036055710281⟩, ⟨1404850880554070790, 1405802954183045044⟩, true⟩

def words02 : List Nat := [371285517228465267, 371285516845234120, 371285516226302260, 371285515650288766, 371285515073843985, 371285514391604155, 371285513083007673, 371285512203972297, 371285511324162147, 371285510865035732]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 46120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 46100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362464967294003296, 362464997855420223⟩, ⟨945317695823463624, 946270411625755130⟩, true⟩

def words03 : List Nat := [371285510205565544, 371285509547138525, 371285508888129125, 371285508698748946, 371285508339981820, 371285508125264910, 371285507910053347, 371285507622885805, 371285506976229365, 371285506533608905]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 46130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 46100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362460461709294888, 362460492284342529⟩, ⟨1153239985975259547, 1154193330768809501⟩, true⟩

def words04 : List Nat := [371285506114484126, 371285506116014652, 371285505516032481, 371285504919030970, 371285504321426788, 371285503742080678, 371285502927237490, 371285502581722124, 371285502235719554, 371285501890643045]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 46140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 46100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362485998346790394, 362486028935710934⟩, ⟨(-25451169811107731), (-24497184713580269)⟩, true⟩

def words05 : List Nat := [371285501349794193, 371285500919073450, 371285500523589392, 371285500525120717, 371285500027777432, 371285499417377547, 371285498806385350, 371285498598044373, 371285498232396062, 371285498245632436]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 46150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 46100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362450593755592275, 362450624358323657⟩, ⟨1608902102395078332, 1609856725071620492⟩, true⟩

def words06 : List Nat := [371285498246789785, 371285498200123802, 371285497528059082, 371285497072859018, 371285496616958763, 371285496181971526, 371285495201990092, 371285494126202689, 371285493049825277, 371285492383558044]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 46160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 46100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362444655278632733, 362444685895165319⟩, ⟨1883206561901956419, 1884161821849072153⟩, true⟩

def words07 : List Nat := [371285491629404358, 371285491344152354, 371285491058377316, 371285490773526013, 371285489863621974, 371285489095608473, 371285488326804644, 371285487955067485, 371285487162908023, 371285486281086694]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 46170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 46100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468204139500722, 362468234769739117⟩, ⟨795730849820822241, 796686742773388997⟩, true⟩

def words08 : List Nat := [371285485398637753, 371285484984884515, 371285484365453661, 371285484214666472, 371285484063394017, 371285483837501713, 371285483221815589, 371285483074891348, 371285482927198197, 371285482804871687]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 46180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 46100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362461896134213063, 362461926778441534⟩, ⟨1087139044675944919, 1088095583897936621⟩, true⟩

def words09 : List Nat := [371285482432610843, 371285482044239574, 371285481655261251, 371285481462921420, 371285481035563077, 371285480751628098, 371285480467215925, 371285480115203350, 371285479138739400, 371285478630906858]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 46190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 46100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 46100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk461
