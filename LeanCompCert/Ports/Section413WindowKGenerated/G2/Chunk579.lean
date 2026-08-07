import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk579

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360563463496667997, 360563484779241310⟩, ⟨1067685895197501007, 1068518419779099297⟩, true⟩

def state01 : KState := ⟨⟨360583840070278008, 360583861360463213⟩, ⟨(-112171752498996154), (-111338787150692026)⟩, true⟩

def words00 : List Nat := [360581939010733364, 360581939043704348, 360581939044424505, 360581938947176421, 360581938849780473, 360581938609566627, 360581938652101823, 360581938783972982, 360581938784693302, 360581938776029329]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 57900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 57900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360603864586673652, 360603885884503621⟩, ⟨(-1271979892636302764), (-1271146484542877134)⟩, true⟩

def words01 : List Nat := [360581938801405461, 360581938827008338, 360581939010204627, 360581939057991396, 360581939058753257, 360581938817730449, 360581938632965234, 360581938914235123, 360581939293809318, 360581939673551758]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 57910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 57900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360596814614510859, 360596835920035393⟩, ⟨(-863770235432583209), (-862936381630826751)⟩, true⟩

def words02 : List Nat := [360581939877100869, 360581939877909462, 360581939987581228, 360581940192066421, 360581940192755721, 360581940183011320, 360581940130725107, 360581939928083424, 360581939727474583, 360581939985533472]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 57920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 57900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360546589289463407, 360546610602611832⟩, ⟨2046125301265241486, 2046959596757267228⟩, true⟩

def words03 : List Nat := [360581940373379614, 360581940761379837, 360581940950483230, 360581940951292021, 360581940924455816, 360581940821608306, 360581940718530114, 360581940539682309, 360581940165570292, 360581939556646304]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 57930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 57900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360607729881057825, 360607751201842725⟩, ⟨(-1496709796946550657), (-1495875058960012153)⟩, true⟩

def words04 : List Nat := [360581938947563316, 360581938426281657, 360581938125106564, 360581938122023054, 360581938118876725, 360581937864298387, 360581937666644399, 360581937717341114, 360581937998949707, 360581938445221442]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 57940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 57900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360570199238189896, 360570220566698249⟩, ⟨678392730072713848, 679227915670326998⟩, true⟩

def words05 : List Nat := [360581938710599159, 360581938976048989, 360581939116278883, 360581939444737808, 360581939651699031, 360581939858784965, 360581939915559127, 360581939916368256, 360581939676080556, 360581939474836109]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 57950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 57900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360565096170593640, 360565117506719025⟩, ⟨974158183634856481, 974993810752753985⟩, true⟩

def words06 : List Nat := [360581939302289662, 360581939303098926, 360581939121677641, 360581938785029342, 360581938448260438, 360581938035534972, 360581937771309907, 360581937388735890, 360581937006095805, 360581936444285918]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 57960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 57900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360619574244573289, 360619595588330240⟩, ⟨(-2184231032466908377), (-2183394962908607573)⟩, true⟩

def words07 : List Nat := [360581936154814053, 360581936023420492, 360581936057133498, 360581936342145148, 360581936372783407, 360581936403482829, 360581936731610799, 360581937211164975, 360581937861325987, 360581938511651525]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 57970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 57900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360598249438246110, 360598270789718413⟩, ⟨(-947884776487142420), (-947048259554578194)⟩, true⟩

def words08 : List Nat := [360581938876365092, 360581939046549963, 360581939353926125, 360581939661528140, 360581939892871309, 360581939912748780, 360581939913478638, 360581939720540208, 360581939554797140, 360581939837336931]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 57980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 57900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571411312890724, 360571432671983322⟩, ⟨608672065314417176, 609509024186479858⟩, true⟩

def words09 : List Nat := [360581940417004951, 360581940996813452, 360581941388226393, 360581941557650864, 360581941558340204, 360581941526264517, 360581941658348989, 360581941659158922, 360581941628611536, 360581941448262400]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 57990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 57900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 57900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk579
