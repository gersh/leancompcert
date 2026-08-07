import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk917

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

def state06 : KState := ⟨⟨360581699303523325, 360581754732308280⟩, ⟨16420236526076592, 19854761240855248⟩, true⟩

def words05 : List Nat := [360581972820636101, 360581972551305041, 360581972281590265, 360581972130771316, 360581971945327721, 360581971658314293, 360581971371028513, 360581971202760900, 360581971110375524, 360581971109392422]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 91750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 91700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583413067333600, 360583468508775323⟩, ⟨(-140927852864758641), (-137492166705761407)⟩, true⟩

def words06 : List Nat := [360581971108216285, 360581971040951499, 360581971003177041, 360581970963150259, 360581970922758826, 360581970852897027, 360581970743018416, 360581970558617877, 360581970373967117, 360581970299464040]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 91760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 91700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360557482585144896, 360557538039068360⟩, ⟨2238904467257756663, 2242341298929119883⟩, true⟩

def words07 : List Nat := [360581970435442042, 360581970571671492, 360581970612570760, 360581970613897459, 360581970536200373, 360581970428327386, 360581970320085983, 360581970207977724, 360581970002505180, 360581969737683844]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 91770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 91700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575473761891155, 360575529228332377⟩, ⟨587600453621366508, 591038434235460392⟩, true⟩

def words08 : List Nat := [360581969472560574, 360581969326401819, 360581969239631458, 360581969193180163, 360581969146595529, 360581968994747881, 360581968724175521, 360581968551142533, 360581968377725811, 360581968256921935]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 91780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 91700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360565713528577658, 360565769007690186⟩, ⟨1483489826030348891, 1486928969802062009⟩, true⟩

def words09 : List Nat := [360581968187988426, 360581968027823391, 360581967867414153, 360581967690162126, 360581967571978457, 360581967377695274, 360581967183271818, 360581966911734213, 360581966665930844, 360581966491021364]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 91790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 91700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 91700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk917
