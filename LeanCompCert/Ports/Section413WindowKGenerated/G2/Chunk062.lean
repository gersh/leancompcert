import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk062

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360618576200059306, 360618576399168285⟩, ⟨(-313665742955880036), (-313664905396237014)⟩, true⟩

def state01 : KState := ⟨⟨360566691374795273, 360566691574586113⟩, ⟨7692035618495581, 7692877408954103⟩, true⟩

def words00 : List Nat := [360567993444000369, 360567984028550326, 360567993537722961, 360568011157366843, 360568011807337664, 360568011807409191, 360568001551241368, 360567978150809552, 360567954757902792, 360567930363218795]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 6200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 6200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360406750827004292, 360406751027469207⟩, ⟨1002608589662511395, 1002609435642427161⟩, true⟩

def words01 : List Nat := [360567955638227120, 360567981104499339, 360567990968225289, 360567994990417003, 360567994990477440, 360567981810504476, 360567981107942322, 360567981108013960, 360567968174145826, 360567942255064453]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 6210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 6200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360837102813895997, 360837103015038450⟩, ⟨(-1676665594397248151), (-1676664744199698091)⟩, true⟩

def words02 : List Nat := [360567916344299953, 360567935477538390, 360567951842019866, 360567968201256263, 360567968201322385, 360567962839191116, 360567954406406642, 360567952901392239, 360567975447675823, 360568018639464755]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 6220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 6200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360528934197712321, 360528934399538647⟩, ⟨245156955364771856, 245157809826258482⟩, true⟩

def words03 : List Nat := [360568045578786614, 360568072509472346, 360568109755438466, 360568159885347863, 360568195413121471, 360568230929514072, 360568242496667230, 360568242496739110, 360568228807186452, 360568222510087727]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 6230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 6200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576678200268695, 360576678402771945⟩, ⟨(-53416703903112425), (-53415845214125065)⟩, true⟩

def words04 : List Nat := [360568230009084153, 360568230009156058, 360568218561819728, 360568194069587706, 360568169585186717, 360568138393504511, 360568128931508156, 360568136900758741, 360568136900822887, 360568133234764567]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 6240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 6200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360604411668220354, 360604411871404610⟩, ⟨(-228015036915067514), (-228014173966405652)⟩, true⟩

def words05 : List Nat := [360568133234824067, 360568123497264475, 360568113762799024, 360568103949805543, 360568082811662784, 360568039784568871, 360567996771214369, 360567982062361461, 360567987881878587, 360567993699552445]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 6250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 6200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360689349703981290, 360689349907852402⟩, ⟨(-761549896099510727), (-761549028847748287)⟩, true⟩

def words06 : List Nat := [360567993699616709, 360567986599329569, 360567975483253099, 360567982562711104, 360567982562772586, 360567971608945615, 360567954728555974, 360567924976022066, 360567895232966489, 360567910100987828]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 6260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 6200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360465832213702086, 360465832418254348⟩, ⟨641694723442278160, 641695594968293528⟩, true⟩

def words07 : List Nat := [360567954688452968, 360567999261717337, 360568023755149745, 360568023755222022, 360568023288716858, 360568015190044399, 360568024185425208, 360568029518761560, 360568029518827436, 360568013245478599]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 6270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 6200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360862173742656706, 360862173947892448⟩, ⟨(-1849959021687611265), (-1849958145865866587)⟩, true⟩

def words08 : List Nat := [360567996977295783, 360567983709170868, 360567997831987265, 360568011950323248, 360568011950389999, 360568004191530028, 360568016341613473, 360568034960909485, 360568062954833810, 360568109705980850]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 6280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 6200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360747129529151888, 360747129735080350⟩, ⟨(-1126398102845063056), (-1126397222662750060)⟩, true⟩

def words09 : List Nat := [360568143129873345, 360568176543151361, 360568198618556784, 360568233358229487, 360568261405956887, 360568289444787793, 360568304752069519, 360568308140610230, 360568336525049187, 360568364900504450]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 6290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 6200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 6200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk062
