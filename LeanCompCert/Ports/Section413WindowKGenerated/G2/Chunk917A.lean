import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk917A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581066289199015, 360581121642706965⟩, ⟨75232527970549012, 78660147529687972⟩, true⟩

def state01 : KState := ⟨⟨360576446395696165, 360576501761830083⟩, ⟨498830588356029188, 502259365779903462⟩, true⟩

def words00 : List Nat := [360581979433319808, 360581979348495034, 360581979228915022, 360581979228492268, 360581979227717894, 360581979197415889, 360581979048313922, 360581978787040604, 360581978525518763, 360581978365971179]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 91700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 91700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360571149180174320, 360571204558790527⟩, ⟨984711716057242488, 988141638294687328⟩, true⟩

def words01 : List Nat := [360581978366352927, 360581978426703444, 360581978427887015, 360581978416736601, 360581978408420555, 360581978307779056, 360581978206750723, 360581978176428520, 360581978133648536, 360581978017559549]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 91710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 91700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360567252493715980, 360567307884867685⟩, ⟨1342148892150012791, 1345579964204601109⟩, true⟩

def words02 : List Nat := [360581977901190929, 360581977782542911, 360581977723000555, 360581977706962230, 360581977690820739, 360581977573372763, 360581977337044391, 360581977165156611, 360581976992844301, 360581976804132971]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 91720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 91700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360563685139475539, 360563740543243005⟩, ⟨1669410229686164689, 1672842459047453751⟩, true⟩

def words03 : List Nat := [360581976645401902, 360581976427213642, 360581976208769303, 360581976109398706, 360581976069159338, 360581975947021485, 360581975824752709, 360581975643432328, 360581975343266032, 360581975146023117]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 91730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 91700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360559711802444655, 360559767218713654⟩, ⟨2033952706419132906, 2037386082733405752⟩, true⟩

def words04 : List Nat := [360581974948338360, 360581974786797550, 360581974628118196, 360581974400608856, 360581974172887689, 360581973891586132, 360581973669136185, 360581973502788448, 360581973336323579, 360581973061577234]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 91740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 91700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk917A
