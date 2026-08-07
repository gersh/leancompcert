import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk128

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362506098857622289, 362506100966292853⟩, ⟨(-279122474196781011), (-279104210564003699)⟩, true⟩

def state01 : KState := ⟨⟨362424746914779710, 362424749026897201⟩, ⟨762180925333398637, 762199233104522729⟩, true⟩

def words00 : List Nat := [371284298491968891, 371284298492350626, 371284292577105218, 371284288262920149, 371284283949224080, 371284280872293380, 371284271563144783, 371284262134413819, 371284252706997337, 371284249357350326]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 12800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 12800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362378484557261496, 362378486672816750⟩, ⟨1355229933616173009, 1355248285442774807⟩, true⟩

def words01 : List Nat := [371284244713138521, 371284244233195138, 371284243753201812, 371284243297092132, 371284235944381757, 371284228720559598, 371284221497663309, 371284216788031194, 371284208513833053, 371284200267625079]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 12810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 12800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362514428872166738, 362514430991143286⟩, ⟨(-388032297759542782), (-388013902054143174)⟩, true⟩

def words02 : List Nat := [371284192022538094, 371284189842573186, 371284185448330738, 371284186283385430, 371284186493306590, 371284186493691854, 371284181942602034, 371284182085626179, 371284188285988612, 371284190643387528]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 12820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 12800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362514597546617670, 362514599669091373⟩, ⟨(-390175168824013845), (-390156728232593923)⟩, true⟩

def words03 : List Nat := [371284192040186792, 371284193436895991, 371284199338595500, 371284202902306989, 371284206794711974, 371284210686652261, 371284213358047544, 371284213358437188, 371284213630590456, 371284215997396599]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 12830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 12800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362460619262567884, 362460621388452968⟩, ⟨303337474494520106, 303355958905827878⟩, true⟩

def words04 : List Nat := [371284224410311280, 371284224757911129, 371284224997064198, 371284225236305377, 371284225678315821, 371284225678737523, 371284225001876633, 371284226918664858, 371284228855675193, 371284228856072099]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 12840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 12800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362482910783104731, 362482912912455476⟩, ⟨17130310651266436, 17148839613848036⟩, true⟩

def words05 : List Nat := [371284230294014573, 371284233568667934, 371284242876945118, 371284244135425154, 371284244396939464, 371284244658535230, 371284247103332518, 371284247103754498, 371284246518033484, 371284246414758264]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 12850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 12800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362448590137528906, 362448592270346380⟩, ⟨458413540934441363, 458432114496372385⟩, true⟩

def words06 : List Nat := [371284246311362330, 371284246110999033, 371284239047041721, 371284236456148291, 371284233865464194, 371284232807692367, 371284226773500358, 371284220755973599, 371284214739231123, 371284212481262960]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 12860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 12800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362405597451570915, 362405599587851122⟩, ⟨1012211942887967018, 1012230561032656830⟩, true⟩

def words07 : List Nat := [371284211860471369, 371284214006982836, 371284214917435902, 371284214917819963, 371284209050748733, 371284204704216671, 371284201021434310, 371284201021818520, 371284195018809665, 371284188917123844]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 12870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 12800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362436479229835111, 362436481369552985⟩, ⟨614431945274479536, 614450607714133516⟩, true⟩

def words08 : List Nat := [371284182816204498, 371284179781762626, 371284174675664970, 371284173476032189, 371284172276470139, 371284170097200867, 371284161862971504, 371284155957863931, 371284150151755260, 371284150152152996]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 12880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 12800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482759272330661, 362482761415549294⟩, ⟨17781390891918800, 17800098474021302⟩, true⟩

def words09 : List Nat := [371284146454606590, 371284142774971852, 371284141415901563, 371284141604887148, 371284143593440821, 371284145581840160, 371284147474525359, 371284147474910124, 371284141374646033, 371284141268144180]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 12890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 12800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 12800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk128
