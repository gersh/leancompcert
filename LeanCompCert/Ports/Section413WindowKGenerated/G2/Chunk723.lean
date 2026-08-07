import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk723

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360577034973813620, 360577068750960332⟩, ⟨381004834680456653, 382654334445557597⟩, true⟩

def state01 : KState := ⟨⟨360577325791562300, 360577359578390999⟩, ⟨359871921505621746, 361522121326986456⟩, true⟩

def words00 : List Nat := [360582361269661482, 360582361263152215, 360582361065618979, 360582360691522004, 360582360317268091, 360582359894816511, 360582359599782369, 360582359495899599, 360582359391907967, 360582359192847188]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 72300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 72300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607766825885398, 360607800622401512⟩, ⟨(-1841441012276342510), (-1839790111909734708)⟩, true⟩

def words01 : List Nat := [360582359209497169, 360582359295588088, 360582359572284879, 360582359900856099, 360582360067525744, 360582360234261707, 360582360396956833, 360582360693073255, 360582361045676259, 360582361398498224]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 72310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 72300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598201401942777, 360598235208231450⟩, ⟨(-1149760324624308825), (-1148108717458067157)⟩, true⟩

def words02 : List Nat := [360582361655988730, 360582361722719984, 360582361904095908, 360582362085798718, 360582362136257410, 360582362137285469, 360582362137240262, 360582362042168554, 360582362004828038, 360582362225451480]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 72320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 72300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574451843782893, 360574485659758110⟩, ⟨568133841204314650, 569786149046021412⟩, true⟩

def words03 : List Nat := [360582362441947058, 360582362658623752, 360582362750111365, 360582362751138416, 360582362718550641, 360582362509706066, 360582362300558314, 360582362282384242, 360582362269500387, 360582362161680229]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 72330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 72300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599267855215693, 360599301680880791⟩, ⟨(-1227138187719654563), (-1225485178863601567)⟩, true⟩

def words04 : List Nat := [360582362135486849, 360582362313910739, 360582362633714683, 360582362953706325, 360582363098292823, 360582363115023248, 360582363161274503, 360582363207820255, 360582363391234839, 360582363626412110]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 72340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 72300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360607220903668874, 360607254739145470⟩, ⟨(-1802581012888386252), (-1800927294124208740)⟩, true⟩

def words05 : List Nat := [360582363765006396, 360582363903723082, 360582364232879411, 360582364668922373, 360582365017825618, 360582365366885921, 360582365607472479, 360582365956257883, 360582366301060853, 360582366646193131]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 72350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 72300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360610983590395658, 360611017435541300⟩, ⟨(-2074864159639086606), (-2073209741173447182)⟩, true⟩

def words06 : List Nat := [360582367162608862, 360582367546164754, 360582367834558242, 360582368123055760, 360582368318000549, 360582368659085685, 360582369190438696, 360582369721973725, 360582370070360341, 360582370467264319]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 72360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 72300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360614537780433158, 360614571635293051⟩, ⟨(-2332220204955279955), (-2330565083422980763)⟩, true⟩

def words07 : List Nat := [360582370840026670, 360582371213075103, 360582371571426666, 360582371739377920, 360582371746066869, 360582371752834354, 360582371912809797, 360582372168286830, 360582372613984626, 360582373059929034]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 72370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 72300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360607726229230724, 360607760093871556⟩, ⟨(-1839292460070524001), (-1837636630544975317)⟩, true⟩

def words08 : List Nat := [360582373384598624, 360582373518829035, 360582373843386950, 360582374168243798, 360582374416310505, 360582374601400286, 360582374637933955, 360582374674552962, 360582374865033439, 360582375216876557]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 72380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 72300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586067773717053, 360586101648032479⟩, ⟨(-271289483731383553), (-269632953812024389)⟩, true⟩

def words09 : List Nat := [360582375598086031, 360582375979476127, 360582376243963038, 360582376513949992, 360582376735366650, 360582376957060170, 360582377235095925, 360582377382541855, 360582377434897975, 360582377487401935]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 72390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 72300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 72300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk723
