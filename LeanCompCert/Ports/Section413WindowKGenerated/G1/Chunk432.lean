import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk432

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479929857588025, 362479956505565357⟩, ⟨237691077356811762, 238468911242779632⟩, true⟩

def state01 : KState := ⟨⟨362482096162430255, 362482122823090954⟩, ⟨144114094060699968, 144892475934963786⟩, true⟩

def words00 : List Nat := [371285476901211890, 371285476902637233, 371285476598043996, 371285476291746638, 371285475984904883, 371285475838480846, 371285475669576383, 371285475854384710, 371285476037905040, 371285476039381974]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 43200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 43200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362509143598174500, 362509170271732392⟩, ⟨(-1024735987565373643), (-1023957048338959439)⟩, true⟩

def words01 : List Nat := [371285476106164418, 371285476251254343, 371285476863100925, 371285477061555525, 371285477148933974, 371285477236770892, 371285477705631858, 371285477979937404, 371285478529090700, 371285479078832206]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 43210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 43200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489225764687291, 362489252451094876⟩, ⟨(-163872984339854108), (-163093489683303336)⟩, true⟩

def words02 : List Nat := [371285479626028300, 371285479627454539, 371285479829135129, 371285480199100027, 371285480583539606, 371285480584965887, 371285480255897165, 371285479929051980, 371285479757121763, 371285479846027140]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 43220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 43200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474592348000387, 362474619047281848⟩, ⟨468874363365952058, 469654414625183132⟩, true⟩

def words03 : List Nat := [371285480270428920, 371285480695434975, 371285481117974955, 371285481119401662, 371285480828625847, 371285480698503609, 371285480971207722, 371285480972641294, 371285480869818568, 371285480620238028]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 43230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 43200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362498519674635786, 362498546386685924⟩, ⟨(-565836065285509517), (-565055461844320075)⟩, true⟩

def words04 : List Nat := [371285480394326193, 371285480395897941, 371285480391950842, 371285480630155351, 371285480812675194, 371285480814126971, 371285480723946572, 371285480896455806, 371285481519037133, 371285481822586960]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 43240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 43200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490427364782011, 362490454089834144⟩, ⟨(-215805715855466338), (-215024550012294420)⟩, true⟩

def words05 : List Nat := [371285482131013455, 371285482439899413, 371285482874158041, 371285483054722769, 371285483309859906, 371285483565543173, 371285483818850275, 371285483820278248, 371285483571409225, 371285483688086328]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 43250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 43200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362465428343987966, 362465455081749634⟩, ⟨865840217614020802, 866621933337031082⟩, true⟩

def words06 : List Nat := [371285484338713674, 371285484342746944, 371285484343835355, 371285484220907951, 371285484097415164, 371285484025407391, 371285483687240917, 371285483566136466, 371285483444567521, 371285483321484717]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 43260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 43200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362517126548429136, 362517153299111294⟩, ⟨(-1371359055563565423), (-1370576780705054279)⟩, true⟩

def words07 : List Nat := [371285482931351775, 371285483004838493, 371285483555389670, 371285483817079477, 371285483978980128, 371285484141304696, 371285484650246493, 371285484894275256, 371285485626954459, 371285486360253480]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 43270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 43200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362508618057081094, 362508644820679393⟩, ⟨(-1003125048567241386), (-1002342214633086348)⟩, true⟩

def words08 : List Nat := [371285486964758391, 371285487187424057, 371285487943843104, 371285488700950580, 371285489478572223, 371285489683366044, 371285489864745554, 371285490046637922, 371285490690714736, 371285491227215785]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 43280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 43200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485818102304488, 362485844878743109⟩, ⟨(-15871636996420476), (-15088247139695384)⟩, true⟩

def words09 : List Nat := [371285492297094479, 371285493367491612, 371285494435423547, 371285494792456818, 371285495177031729, 371285495562309479, 371285496341309764, 371285496409657719, 371285496418786605, 371285496428426958]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 43290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 43200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 43200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk432
