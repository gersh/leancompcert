import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk771

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490090226006591, 362490179110471113⟩, ⟨(-388442034580886186), (-383814270196418448)⟩, true⟩

def state01 : KState := ⟨⟨362491142024201619, 362491230932324231⟩, ⟨(-469524127276697812), (-464894538730445956)⟩, true⟩

def words00 : List Nat := [371285201273682998, 371285201334494578, 371285201396302991, 371285201459015322, 371285201527487214, 371285201530417362, 371285201663638325, 371285201807674966, 371285201950967418, 371285202031924412]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 77100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 77100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362499151213114008, 362499240145341255⟩, ⟨(-1087128877347069810), (-1082497429978135558)⟩, true⟩

def words01 : List Nat := [371285202236135045, 371285202441839533, 371285202783654026, 371285202902313669, 371285202982011134, 371285203062523586, 371285203285473449, 371285203425400009, 371285203609249210, 371285203794282813]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 77110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 77100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483861416918674, 362483950373144290⟩, ⟨92060786779762019, 96694085026503969⟩, true⟩

def words02 : List Nat := [371285203931603342, 371285203934262747, 371285203909303750, 371285203974353906, 371285204087541895, 371285204090248526, 371285204065140741, 371285204029921168, 371285204020866849, 371285204023929024]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 77120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 77100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475250212690425, 362475339192866517⟩, ⟨756332790229187454, 760967935898459164⟩, true⟩

def words03 : List Nat := [371285204141345892, 371285204276090526, 371285204376760698, 371285204379420408, 371285204256048937, 371285204185410955, 371285204207405668, 371285204210065442, 371285204082256327, 371285203957397221]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 77130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 77100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482447748246028, 362482536752213336⟩, ⟨201129377012392198, 205766358058554648⟩, true⟩

def words04 : List Nat := [371285203871327886, 371285203874278539, 371285203941374922, 371285204020562682, 371285204060337665, 371285204063005353, 371285203930536820, 371285203852118209, 371285203844181193, 371285203846938658]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 77140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 77100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486128883410431, 362486217911638993⟩, ⟨(-82850479418298569), (-78211626492193185)⟩, true⟩

def words05 : List Nat := [371285203814357481, 371285203782846474, 371285203883610923, 371285203976335106, 371285204099730973, 371285204224109933, 371285204346561542, 371285204349222583, 371285204279151765, 371285204295608976]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 77150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 77100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468909219956900, 362468998271930237⟩, ⟨1245896117336480020, 1250536802529954794⟩, true⟩

def words06 : List Nat := [371285204363520487, 371285204366182751, 371285204238888959, 371285204088876623, 371285203937888558, 371285203766456799, 371285203509459409, 371285203421440514, 371285203332426155, 371285203232439891]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 77160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 77100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493788725768446, 362493877801744542⟩, ⟨(-674179360375871410), (-669536822768331980)⟩, true⟩

def words07 : List Nat := [371285203024257211, 371285202985211991, 371285203049387199, 371285203052049643, 371285202964984781, 371285202837182647, 371285202724703411, 371285202727642730, 371285202794589113, 371285202909960705]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 77170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 77100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481461879048040, 362481550979076053⟩, ⟨277275640270259751, 281920034322964371⟩, true⟩

def words08 : List Nat := [371285203021557092, 371285203024267021, 371285203155054101, 371285203297647232, 371285203475300945, 371285203477963114, 371285203432158080, 371285203353830105, 371285203274472201, 371285203266086326]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 77180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 77100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481460629707736, 362481549753742223⟩, ⟨277427026004751702, 282073273239693352⟩, true⟩

def words09 : List Nat := [371285203340946938, 371285203464226790, 371285203583688413, 371285203586363763, 371285203552732706, 371285203563836668, 371285203639655614, 371285203642339039, 371285203596916836, 371285203552618385]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 77190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 77100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 77100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk771
