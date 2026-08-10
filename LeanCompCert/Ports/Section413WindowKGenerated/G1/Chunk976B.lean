import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk976A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk976B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk976A

def state06 : KState := ⟨⟨362478327015552518, 362478472248022107⟩, ⟨662027892215237480, 671603825118887432⟩, true⟩

def words05 : List Nat := [371285349349779329, 371285349415035480, 371285349475977134, 371285349479405368, 371285349409792619, 371285349373647841, 371285349337879966, 371285349341336684, 371285349273706068, 371285349207116096]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 97650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 97600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482575479124569, 362482720742281588⟩, ⟨247152698551051453, 256731628544298697⟩, true⟩

def words06 : List Nat := [371285349158269844, 371285349162049997, 371285349204199786, 371285349275034152, 371285349316137509, 371285349319567351, 371285349247114982, 371285349258296032, 371285349300506558, 371285349304056384]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 97660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 97600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486256515488700, 362486401809948879⟩, ⟨(-112383451868573166), (-102801464342487118)⟩, true⟩

def words07 : List Nat := [371285349279751313, 371285349236175645, 371285349248721614, 371285349263606069, 371285349309183848, 371285349356041301, 371285349401897253, 371285349405386317, 371285349374576504, 371285349389679406]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 97670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 97600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483816434774434, 362483961759733724⟩, ⟨125989056702398231, 135574023542444131⟩, true⟩

def words08 : List Nat := [371285349459013049, 371285349462468331, 371285349454975070, 371285349448386533, 371285349440556882, 371285349440025179, 371285349442980745, 371285349499476203, 371285349554561264, 371285349558111680]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 97680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 97600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489817327574410, 362489962683545163⟩, ⟨(-460262174862779754), (-450674178357563786)⟩, true⟩

def words09 : List Nat := [371285349575547213, 371285349608985143, 371285349738218495, 371285349741648155, 371285349731574596, 371285349710932503, 371285349759359180, 371285349793096383, 371285349842683855, 371285349893723590]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 97690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 97600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 97600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk976B
