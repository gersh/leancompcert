import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk716A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk716B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk716A

def state06 : KState := ⟨⟨362496393756930817, 362496470105745872⟩, ⟨(-807715117804413366), (-804020201238189000)⟩, true⟩

def words05 : List Nat := [371285249163437851, 371285249252199681, 371285249513700653, 371285249601326618, 371285249641470449, 371285249682408547, 371285249895867544, 371285250014493136, 371285250172764869, 371285250332072072]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483107643341898, 362483184014322137⟩, ⟨144410515458905275, 148107020496985151⟩, true⟩

def words06 : List Nat := [371285250490873012, 371285250493330696, 371285250484666286, 371285250579723996, 371285250681742723, 371285250684243395, 371285250624247144, 371285250564881621, 371285250524989907, 371285250527793562]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472050539945494, 362472126933121552⟩, ⟨936988935519629873, 940687031440984473⟩, true⟩

def words07 : List Nat := [371285250666267900, 371285250834602382, 371285250962068496, 371285250964526676, 371285250832542974, 371285250737289172, 371285250716535698, 371285250718993941, 371285250537348582, 371285250357109289]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472304447041864, 362472380862200685⟩, ⟨918857424671834364, 922557096428374708⟩, true⟩

def words08 : List Nat := [371285250175696592, 371285250157933429, 371285250134872884, 371285250206361400, 371285250232998435, 371285250235457296, 371285250031525979, 371285249834370562, 371285249635926352, 371285249562109018]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484361285777189, 362484437723312480⟩, ⟨54441244348775396, 58142520390396170⟩, true⟩

def words09 : List Nat := [371285249384447526, 371285249193605260, 371285249002644647, 371285249005427118, 371285248936741332, 371285248907845862, 371285248878088875, 371285248849369706, 371285248645413779, 371285248637125457]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk716B
