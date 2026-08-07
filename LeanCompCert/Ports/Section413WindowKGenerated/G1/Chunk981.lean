import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk981

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362495418626882266, 362495565221737825⟩, ⟨(-1011045531178622523), (-1001336247546502461)⟩, true⟩

def state01 : KState := ⟨⟨362484743635511834, 362484890260987593⟩, ⟨36260557010550802, 45972844647419844⟩, true⟩

def words00 : List Nat := [371285358234921933, 371285358318094626, 371285358398341588, 371285358479781624, 371285358566103269, 371285358606811126, 371285358691784472, 371285358778119768, 371285358842117864, 371285358845684846]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 98100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 98100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492348637303153, 362492495294028706⟩, ⟨(-709897028236380799), (-700181674534632521)⟩, true⟩

def words01 : List Nat := [371285358906995768, 371285358974983149, 371285359120645426, 371285359128946284, 371285359131614236, 371285359127743208, 371285359200646196, 371285359241955195, 371285359317060257, 371285359393716494]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 98110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 98100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362493393891284282, 362493540579070830⟩, ⟨(-812502649066609129), (-802784247500858899)⟩, true⟩

def words02 : List Nat := [371285359468837473, 371285359472283776, 371285359473702214, 371285359529315937, 371285359611356282, 371285359620735984, 371285359629304177, 371285359639058342, 371285359751257274, 371285359838555592]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 98120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 98100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479379680098227, 362479526398915567⟩, ⟨562810055665394923, 572531502442174175⟩, true⟩

def words03 : List Nat := [371285359976194588, 371285360115187428, 371285360233002376, 371285360236448961, 371285360235526916, 371285360250360769, 371285360331847677, 371285360335294254, 371285360278606467, 371285360223069248]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 98130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 98100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485195171628909, 362485341921282305⟩, ⟨(-7939142914805034), 1785330271438640⟩, true⟩

def words04 : List Nat := [371285360165972507, 371285360149810660, 371285360142045335, 371285360192716757, 371285360225663895, 371285360229113536, 371285360144871773, 371285360104668490, 371285360107506501, 371285360111096584]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 98140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 98100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488842973295445, 362488989754382228⟩, ⟨(-365989065372556075), (-356261506842720451)⟩, true⟩

def words05 : List Nat := [371285360113487088, 371285360116899168, 371285360171620402, 371285360200806423, 371285360255332286, 371285360311148100, 371285360365662423, 371285360369119082, 371285360354108112, 371285360395402158]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 98150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 98100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477236115366289, 362477382927177919⟩, ⟨773385757685350882, 783116332326512770⟩, true⟩

def words06 : List Nat := [371285360462930695, 371285360466378042, 371285360395807974, 371285360325109798, 371285360253093818, 371285360204012562, 371285360101668558, 371285360093404920, 371285360083880430, 371285360072256116]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 98160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 98100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489862610757699, 362490009453702033⟩, ⟨(-466226991730896613), (-456493360639840415)⟩, true⟩

def words07 : List Nat := [371285360005239873, 371285360021275865, 371285360111810991, 371285360115258885, 371285360077472085, 371285359990431008, 371285359901920283, 371285359901078593, 371285359894343507, 371285359945542208]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 98170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 98100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482425422664914, 362482572296760260⟩, ⟨263996370310570699, 273733059970909551⟩, true⟩

def words08 : List Nat := [371285359995594139, 371285359999102383, 371285360011269216, 371285360064035358, 371285360142401487, 371285360145873137, 371285360131494964, 371285360108699395, 371285360084583552, 371285360086351572]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 98180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 98100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474682142208531, 362474829047380888⟩, ⟨1024396267066656669, 1034136008332351029⟩, true⟩

def words09 : List Nat := [371285360125149818, 371285360193806898, 371285360259054260, 371285360262505701, 371285360215384522, 371285360186525909, 371285360168412481, 371285360171862850, 371285360067292055, 371285359963962684]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 98190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 98100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 98100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk981
