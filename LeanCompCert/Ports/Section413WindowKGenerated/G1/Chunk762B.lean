import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk762A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk762B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk762A

def state06 : KState := ⟨⟨362488070417913252, 362488157302530598⟩, ⟨(-229916786309881168), (-225442372116827968)⟩, true⟩

def words05 : List Nat := [371285201477937989, 371285201343938608, 371285201243927661, 371285201246822718, 371285201206356155, 371285201198288843, 371285201189316586, 371285201158285819, 371285201065730938, 371285201107724383]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 76250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 76200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485523039603271, 362485609947595951⟩, ⟨(-35621003188980416), (-31144806270141686)⟩, true⟩

def words06 : List Nat := [371285201320129893, 371285201357419366, 371285201360517899, 371285201364514447, 371285201375188935, 371285201378117746, 371285201412689584, 371285201504560391, 371285201595505602, 371285201603582235]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 76260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 76200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499870315649627, 362499957247454974⟩, ⟨(-1129928035389283118), (-1125450022158456572)⟩, true⟩

def words07 : List Nat := [371285201724655095, 371285201847169880, 371285202118951670, 371285202237344393, 371285202335151800, 371285202433728179, 371285202686180275, 371285202853874472, 371285203049116945, 371285203245512702]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 76270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 76200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495159610608695, 362495246566123817⟩, ⟨(-770619247814452085), (-766139425881273889)⟩, true⟩

def words08 : List Nat := [371285203430894961, 371285203433524197, 371285203572309220, 371285203729850692, 371285203891832541, 371285203911744709, 371285203917375531, 371285203923932038, 371285204101126941, 371285204235758751]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 76280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 76200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478786821731736, 362478873800926015⟩, ⟨478587642266578084, 483069270800776824⟩, true⟩

def words09 : List Nat := [371285204461956805, 371285204689191166, 371285204881513174, 371285204884143293, 371285204922494879, 371285204970048246, 371285205130083993, 371285205132712802, 371285205064024879, 371285204984029564]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 76290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 76200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 76200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk762B
