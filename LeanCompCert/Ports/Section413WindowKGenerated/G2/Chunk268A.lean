import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk268A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk268A
