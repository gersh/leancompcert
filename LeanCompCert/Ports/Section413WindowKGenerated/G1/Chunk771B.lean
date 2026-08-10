import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk771A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk771B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk771A

def state06 : KState := ⟨⟨362486128883410431, 362486217911638993⟩, ⟨(-82850479418298569), (-78211626492193185)⟩, true⟩

def words05 : List Nat := [371285203814357481, 371285203782846474, 371285203883610923, 371285203976335106, 371285204099730973, 371285204224109933, 371285204346561542, 371285204349222583, 371285204279151765, 371285204295608976]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 77150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 77100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468909219956900, 362468998271930237⟩, ⟨1245896117336480020, 1250536802529954794⟩, true⟩

def words06 : List Nat := [371285204363520487, 371285204366182751, 371285204238888959, 371285204088876623, 371285203937888558, 371285203766456799, 371285203509459409, 371285203421440514, 371285203332426155, 371285203232439891]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 77160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 77100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493788725768446, 362493877801744542⟩, ⟨(-674179360375871410), (-669536822768331980)⟩, true⟩

def words07 : List Nat := [371285203024257211, 371285202985211991, 371285203049387199, 371285203052049643, 371285202964984781, 371285202837182647, 371285202724703411, 371285202727642730, 371285202794589113, 371285202909960705]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 77170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 77100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481461879048040, 362481550979076053⟩, ⟨277275640270259751, 281920034322964371⟩, true⟩

def words08 : List Nat := [371285203021557092, 371285203024267021, 371285203155054101, 371285203297647232, 371285203475300945, 371285203477963114, 371285203432158080, 371285203353830105, 371285203274472201, 371285203266086326]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 77180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 77100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481460629707736, 362481549753742223⟩, ⟨277427026004751702, 282073273239693352⟩, true⟩

def words09 : List Nat := [371285203340946938, 371285203464226790, 371285203583688413, 371285203586363763, 371285203552732706, 371285203563836668, 371285203639655614, 371285203642339039, 371285203596916836, 371285203552618385]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 77190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 77100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 77100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk771B
