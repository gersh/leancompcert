import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk268

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360529616447504013, 360529620725584629⟩, ⟨1418378589245495522, 1418456142086376912⟩, true⟩

def state01 : KState := ⟨⟨360566875315752986, 360566879597162186⟩, ⟨419749573047945475, 419827215111713435⟩, true⟩

def words00 : List Nat := [360582546219026044, 360582545757109322, 360582545789766557, 360582545822483564, 360582545822808310, 360582544681705232, 360582543149758109, 360582541828040825, 360582540506320761, 360582538948714283]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 26800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 26800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360585189151151281, 360585193435916880⟩, ⟨(-71339002355756895), (-71261270290389687)⟩, true⟩

def words01 : List Nat := [360582538364966977, 360582537044079231, 360582535790474729, 360582536722242772, 360582537044687676, 360582537367165661, 360582537367485067, 360582536611033298, 360582536415739574, 360582536515209584]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 26810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 26800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360578682226787795, 360578686514870863⟩, ⟨103193493133531895, 103271314190294437⟩, true⟩

def words02 : List Nat := [360582538002177698, 360582538104564835, 360582538104878940, 360582537506776079, 360582536908655217, 360582535447923020, 360582535546785466, 360582536118369603, 360582536118688703, 360582535613424359]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 26820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 26800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360638060582612918, 360638064874028722⟩, ⟨(-1490479733835993692), (-1490401823345433500)⟩, true⟩

def words03 : List Nat := [360582535470257349, 360582535289691621, 360582536314323303, 360582536314675849, 360582536136719840, 360582534789030616, 360582533441374665, 360582533675367757, 360582535744624714, 360582537813809452]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 26830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 26800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579150725280602, 360579155020052054⟩, ⟨90535964934493353, 90613965507317913⟩, true⟩

def words04 : List Nat := [360582538999658131, 360582539000010808, 360582539060321109, 360582539318131240, 360582539318433119, 360582538312377429, 360582536525590317, 360582533835937280, 360582531146417324, 360582529841858659]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 26840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 26800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360515589288379380, 360515593586479181⟩, ⟨1797536394868351287, 1797614484824064621⟩, true⟩

def words05 : List Nat := [360582529801002331, 360582529885898256, 360582529886212766, 360582529272542982, 360582527947228264, 360582525900771309, 360582523854360258, 360582522829036580, 360582521412347145, 360582518920984917]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360667811801054178, 360667816102484693⟩, ⟨(-2291820029671140903), (-2291741850235971955)⟩, true⟩

def words06 : List Nat := [360582516429727677, 360582515405700777, 360582516872816471, 360582518339890816, 360582518665759055, 360582519582541672, 360582521443132865, 360582523303688599, 360582526118857895, 360582529293276403]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611963648898681, 360611967953696846⟩, ⟨(-791045632093251038), (-790967362152386574)⟩, true⟩

def words07 : List Nat := [360582531531536743, 360582533769667378, 360582535243706716, 360582537418277683, 360582539036381284, 360582540654421470, 360582541275657129, 360582541276010321, 360582542084160011, 360582543179240822]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566510470490585, 360566514778613190⟩, ⟨430986892107386184, 431065251426118746⟩, true⟩

def words08 : List Nat := [360582545655635262, 360582546753750028, 360582546942165533, 360582547130606357, 360582547130902739, 360582546935432064, 360582546935723255, 360582546678894355, 360582546422046186, 360582545468513753]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360669994067517452, 360669998378975845⟩, ⟨(-2352125019726470393), (-2352046570691989639)⟩, true⟩

def words09 : List Nat := [360582545657256012, 360582546442182875, 360582548607525552, 360582551400465926, 360582552792624259, 360582554184704634, 360582555970795045, 360582558452278215, 360582561703119299, 360582564953798641]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk268
