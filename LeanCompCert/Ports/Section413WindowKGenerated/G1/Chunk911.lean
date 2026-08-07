import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk911

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489475396725456, 362489601096399527⟩, ⟨(-417048785629820444), (-409317154298554668)⟩, true⟩

def state01 : KState := ⟨⟨362477253543034862, 362477379271409226⟩, ⟨696395622504444917, 704129868576129687⟩, true⟩

def words00 : List Nat := [371285108144070183, 371285108147275387, 371285108111308797, 371285108118670981, 371285108126526117, 371285108129708299, 371285107977160744, 371285107824635681, 371285107670848943, 371285107620312488]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 91100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 91100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362465202648469328, 362465328405569638⟩, ⟨1794465327380662080, 1802202190818177798⟩, true⟩

def words01 : List Nat := [371285107564702872, 371285107595300758, 371285107599409810, 371285107602592238, 371285107446046300, 371285107327969850, 371285107208255666, 371285107148410705, 371285106957354949, 371285106743923657]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 91110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 91100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489305334877857, 362489431120458403⟩, ⟨(-401880854585644950), (-394141395883066000)⟩, true⟩

def words02 : List Nat := [371285106529025995, 371285106435816992, 371285106281134035, 371285106241973431, 371285106201849197, 371285106143362239, 371285106005234202, 371285105989107224, 371285106071653091, 371285106122423892]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 91120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 91100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482562271277359, 362482688085862000⟩, ⟨212645954513594092, 220388056501190764⟩, true⟩

def words03 : List Nat := [371285106159595418, 371285106197811443, 371285106274115175, 371285106299401809, 371285106329331290, 371285106360510881, 371285106376484356, 371285106379667716, 371285106234993815, 371285106212442000]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 91130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 91100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473195065508007, 362473320908412581⟩, ⟨1066455341953316513, 1074200025168941197⟩, true⟩

def words04 : List Nat := [371285106281832174, 371285106285015700, 371285106231714439, 371285106168948801, 371285106104936466, 371285106079079992, 371285106009113515, 371285105969099559, 371285105928043463, 371285105878518659]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 91140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 91100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362496522995855177, 362496648867577565⟩, ⟨(-1059984679270271837), (-1052237369168676897)⟩, true⟩

def words05 : List Nat := [371285105751386923, 371285105746265566, 371285105850666075, 371285105887968591, 371285105895317390, 371285105903644544, 371285105972246511, 371285105982124883, 371285106110906272, 371285106241134584]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 91150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 91100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488519548454597, 362488645448973993⟩, ⟨(-330376487925487112), (-322626552544159418)⟩, true⟩

def words06 : List Nat := [371285106345361144, 371285106348552232, 371285106425422789, 371285106526677090, 371285106663248155, 371285106666432874, 371285106657502679, 371285106649697057, 371285106709400816, 371285106751882329]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 91160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 91100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472845251506732, 362472971180626032⟩, ⟨1098763880002757158, 1106516422983579854⟩, true⟩

def words07 : List Nat := [371285106850757539, 371285106950895573, 371285107049900829, 371285107053085395, 371285106991687533, 371285106937353333, 371285106931499580, 371285106934684203, 371285106826984796, 371285106697438750]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 91170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 91100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483277955201314, 362483403912884707⟩, ⟨147499157678844105, 155254305276952043⟩, true⟩

def words08 : List Nat := [371285106566510334, 371285106525229590, 371285106495521220, 371285106543179362, 371285106570526553, 371285106573711834, 371285106453598285, 371285106436557625, 371285106446084852, 371285106449404907]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 91180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 91100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485467225571155, 362485593212288661⟩, ⟨(-52137111259131682), (-44379315897299682)⟩, true⟩

def words09 : List Nat := [371285106433115803, 371285106419243196, 371285106506850997, 371285106553150600, 371285106600607895, 371285106649301314, 371285106697105542, 371285106700291159, 371285106592973440, 371285106602318406]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 91190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 91100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 91100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk911
