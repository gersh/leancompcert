import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk404A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk404B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk404A

def state06 : KState := ⟨⟨360585569471129077, 360585579563856974⟩, ⟨(-121078463523669944), (-120802474176732748)⟩, true⟩

def words05 : List Nat := [360582599583962636, 360582599282440250, 360582598980779962, 360582598662959247, 360582597887558425, 360582596595843342, 360582595304085288, 360582594298704400, 360582593837272540, 360582593911644307]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 40450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 40400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360524372740110344, 360524382838059932⟩, ⟨2355150259170000226, 2355426459812263932⟩, true⟩

def words06 : List Nat := [360582593912133087, 360582593680861139, 360582592841353750, 360582592383912178, 360582591926342593, 360582591313478076, 360582590092510559, 360582588337329808, 360582586582135869, 360582584628517364]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 40460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 40400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360515590465760506, 360515600568876116⟩, ⟨2710772874844298729, 2711049284581620829⟩, true⟩

def words07 : List Nat := [360582583190850258, 360582582362399238, 360582581533934248, 360582580396923507, 360582579380996598, 360582578211484578, 360582577041870903, 360582576077329986, 360582574784182786, 360582573130254121]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 40470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 40400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360561479663435424, 360561489771737390⟩, ⟨852933868025003789, 853210487732026035⟩, true⟩

def words08 : List Nat := [360582571476286133, 360582569806696669, 360582568527793772, 360582567857736120, 360582567187668289, 360582565999278879, 360582564451779734, 360582563513133401, 360582562574363315, 360582561900355124]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 40480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 40400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360550841478536326, 360550851592070086⟩, ⟨1283718223943705408, 1283995055511410880⟩, true⟩

def words09 : List Nat := [360582561380437004, 360582560394840481, 360582559409187497, 360582559087013700, 360582559087483525, 360582558608836594, 360582558130153402, 360582557346560117, 360582555955878276, 360582555173687652]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 40490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 40400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 40400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk404B
