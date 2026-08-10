import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk207A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk207B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk207A

def state06 : KState := ⟨⟨360526661882441754, 360526664392252545⟩, ⟨1131654231874449885, 1131689490077581195⟩, true⟩

def words05 : List Nat := [360581197392569988, 360581194332965984, 360581191273605925, 360581190940077492, 360581190940304463, 360581189697157818, 360581188454104088, 360581184934584542, 360581179999159040, 360581177373470155]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 20750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 20700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360533556016678175, 360533558529004948⟩, ⟨988491757137786237, 988527067585321063⟩, true⟩

def words06 : List Nat := [360581174747947358, 360581172790341225, 360581170933593543, 360581167897918534, 360581164862492217, 360581161243950952, 360581158809524080, 360581157372260176, 360581155935108162, 360581152513963317]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 20760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 20700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360668124239611201, 360668126754457456⟩, ⟨(-1807030373620293452), (-1806995010830467610)⟩, true⟩

def words07 : List Nat := [360581150237652870, 360581150252788547, 360581152573608400, 360581155587658396, 360581156642231120, 360581157696727789, 360581160355151861, 360581164195090249, 360581168380223946, 360581172565013711]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 20770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 20700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360627260384578273, 360627262901973460⟩, ⟨(-958272851902845179), (-958237436134203661)⟩, true⟩

def words08 : List Nat := [360581175576664376, 360581176277664198, 360581176925347328, 360581177573042389, 360581177640490600, 360581177640758305, 360581176805070350, 360581174314330675, 360581171823779601, 360581173852089655]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 20780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 20700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360501198957550138, 360501201477458418⟩, ⟨1663392938487954050, 1663428406516809564⟩, true⟩

def words09 : List Nat := [360581176818086909, 360581179783849756, 360581181267421435, 360581181526949657, 360581181527173345, 360581181208114450, 360581180889012018, 360581180518585955, 360581177841741920, 360581173997002496]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 20790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 20700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 20700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk207B
