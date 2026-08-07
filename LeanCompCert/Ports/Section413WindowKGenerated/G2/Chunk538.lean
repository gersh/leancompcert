import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk538

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360552401439310726, 360552419705903512⟩, ⟨1587923562515538945, 1588587563604671997⟩, true⟩

def state01 : KState := ⟨⟨360552646519858546, 360552664793510911⟩, ⟨1574785284388497247, 1575449665316905943⟩, true⟩

def words00 : List Nat := [360581946807561691, 360581946206624755, 360581945886207025, 360581945840784347, 360581945795306971, 360581945412490905, 360581944684691488, 360581944060150656, 360581943435422673, 360581942802529995]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 53800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 53800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360559609151153226, 360559627431923543⟩, ⟨1200081472094129215, 1200746236074054423⟩, true⟩

def words01 : List Nat := [360581942259112439, 360581941538543364, 360581940817853034, 360581940442084929, 360581940239961647, 360581939888852941, 360581939537662195, 360581939013626804, 360581938255044126, 360581937841363790]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 53810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 53800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360566727981607636, 360566746269420594⟩, ⟨816862460662280642, 817527603712856822⟩, true⟩

def words02 : List Nat := [360581937427437976, 360581937285739727, 360581937030124237, 360581936446608659, 360581935862992957, 360581935190843862, 360581934692138922, 360581934346036174, 360581933999870864, 360581933481081617]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 53820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 53800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360576462647266470, 360576480942129367⟩, ⟨292810073491431703, 293475596075847879⟩, true⟩

def words03 : List Nat := [360581933261880835, 360581933325024439, 360581933339675486, 360581933340427779, 360581933302655235, 360581932918427056, 360581932534080254, 360581932141762008, 360581931926628086, 360581931826157522]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 53830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 53800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569227287028047, 360569245589007605⟩, ⟨682179578307503189, 682845484087730089⟩, true⟩

def words04 : List Nat := [360581931725582971, 360581931423769432, 360581930777516825, 360581930291272444, 360581929804838273, 360581929071566196, 360581928389482743, 360581927511365055, 360581926633136640, 360581926099389922]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 53840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 53800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360539660708169322, 360539679017198104⟩, ⟨2274446304922112465, 2275112590338960853⟩, true⟩

def words05 : List Nat := [360581925864530962, 360581925590646574, 360581925316691337, 360581924830503845, 360581924000009858, 360581923083030218, 360581922165850053, 360581921592969362, 360581921029650265, 360581920246131245]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 53850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 53800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360572944231404470, 360572962547484108⟩, ⟨481696546110241816, 482363211320607338⟩, true⟩

def words06 : List Nat := [360581919462472002, 360581919023141242, 360581918789161506, 360581918792848906, 360581918793558884, 360581918494576975, 360581918040050427, 360581917525438881, 360581917010627158, 360581916755973446]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 53860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 53800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360565853254653821, 360565871577864879⟩, ⟨863737876229977637, 864404925644772331⟩, true⟩

def words07 : List Nat := [360581916590423816, 360581916252381445, 360581915914193144, 360581915690785165, 360581915690965215, 360581915592815438, 360581915494587647, 360581915223939220, 360581915024842334, 360581914727932526]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 53870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 53800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582619842935599, 360582638173190174⟩, ⟨(-39744544341241708), (-39077115386149174)⟩, true⟩

def words08 : List Nat := [360581914476848303, 360581914477596900, 360581914345334322, 360581914040754337, 360581913736065032, 360581913240080763, 360581913123214222, 360581913237101272, 360581913237773139, 360581913059249328]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 53880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 53800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360615057917363068, 360615076254689026⟩, ⟨(-1788086288046856059), (-1787418477979975129)⟩, true⟩

def words09 : List Nat := [360581913417011766, 360581913774988693, 360581914124529331, 360581914130487304, 360581914131177087, 360581913844099887, 360581913612721694, 360581913885194309, 360581914501056552, 360581915117085272]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 53890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 53800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 53800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk538
