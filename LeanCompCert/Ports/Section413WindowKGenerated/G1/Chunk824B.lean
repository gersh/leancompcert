import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk824A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk824B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk824A

def state06 : KState := ⟨⟨362482431306721783, 362482533505967793⟩, ⟨219965112184023114, 225655560246827982⟩, true⟩

def words05 : List Nat := [371285270866643675, 371285270837589591, 371285270834917375, 371285270837774714, 371285270671719037, 371285270469330308, 371285270265736792, 371285270210534242, 371285270081628174, 371285270051689923]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469771280701360, 362469873505696221⟩, ⟨1263941158482058823, 1269633729928880271⟩, true⟩

def words06 : List Nat := [371285270020640127, 371285269990090257, 371285269762595090, 371285269683745373, 371285269603441979, 371285269569001615, 371285269337912213, 371285269044444910, 371285268749846569, 371285268603670380]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477316372979154, 362477418623747842⟩, ⟨641701467397626891, 647396164541648795⟩, true⟩

def words07 : List Nat := [371285268418935719, 371285268382497718, 371285268345055413, 371285268296037609, 371285268141138690, 371285268030527557, 371285267929275140, 371285267932157094, 371285267844718936, 371285267752803876]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483378025061501, 362483480301439512⟩, ⟨141729108372398367, 147425917903095449⟩, true⟩

def words08 : List Nat := [371285267659613455, 371285267627848164, 371285267566004187, 371285267610718356, 371285267641043279, 371285267643901912, 371285267477999428, 371285267460697089, 371285267495932551, 371285267498892575]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493624403971222, 362493726706364728⟩, ⟨(-703551443038367572), (-697852487359090700)⟩, true⟩

def words09 : List Nat := [371285267479365868, 371285267463457847, 371285267574433478, 371285267632357331, 371285267696675475, 371285267762093449, 371285267821909046, 371285267824788130, 371285267884798044, 371285267990866018]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk824B
