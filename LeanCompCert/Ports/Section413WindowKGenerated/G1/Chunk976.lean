import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk976

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484295032890614, 362484440080123163⟩, ⟨78966237219810904, 88524085416136252⟩, true⟩

def state01 : KState := ⟨⟨362487652929616897, 362487798007544985⟩, ⟨(-248799782613123124), (-239238938377903758)⟩, true⟩

def words00 : List Nat := [371285347109669415, 371285347113445249, 371285347102110347, 371285347117123087, 371285347119801752, 371285347117125161, 371285346992042056, 371285346973876317, 371285347036489100, 371285347065147326]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 97600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 97600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488692435874429, 362488837544975943⟩, ⟨(-350240504695592750), (-340676617462907126)⟩, true⟩

def words01 : List Nat := [371285347092589258, 371285347121162989, 371285347253387516, 371285347362669947, 371285347476399924, 371285347591444067, 371285347704595553, 371285347708022186, 371285347716783012, 371285347756739161]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 97610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 97600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488164999253168, 362488310138894914⟩, ⟨(-298723566559740069), (-289156697829077623)⟩, true⟩

def words02 : List Nat := [371285347874884092, 371285347927197886, 371285347978718946, 371285348031403581, 371285348084537875, 371285348091967473, 371285348192461195, 371285348294317638, 371285348374622658, 371285348408524140]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 97620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 97600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362501151368700581, 362501296539362417⟩, ⟨(-1566660540043944573), (-1557090642669137027)⟩, true⟩

def words03 : List Nat := [371285348507422036, 371285348608183474, 371285348800643953, 371285348854362203, 371285348884570320, 371285348915900824, 371285349037409161, 371285349108021499, 371285349273674318, 371285349440882587]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 97630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 97600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480969865323828, 362481115066989487⟩, ⟨403902784826317141, 413475709567323587⟩, true⟩

def words04 : List Nat := [371285349601072404, 371285349622280145, 371285349641256854, 371285349661919974, 371285349697732997, 371285349701160988, 371285349597342265, 371285349473399091, 371285349348006903, 371285349329248241]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 97640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 97600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk976
