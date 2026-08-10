import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk167A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk167B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk167A

def state06 : KState := ⟨⟨360649381244941315, 360649382849368143⟩, ⟨(-1114282027379800673), (-1114263823610438915)⟩, true⟩

def words05 : List Nat := [360582898954867026, 360582901552747628, 360582904651974551, 360582904652185962, 360582904222670399, 360582900795283458, 360582897368266022, 360582895360249140, 360582899327454251, 360582903294233579]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 16750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 16700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360637761449702463, 360637763056142994⟩, ⟨(-919791149260513042), (-919772911731800274)⟩, true⟩

def words06 : List Nat := [360582904865510635, 360582906451622594, 360582911584069429, 360582916715967045, 360582919403972579, 360582919925986852, 360582919926177489, 360582918204998352, 360582916728427402, 360582919998976946]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 16760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 16700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360450743740929070, 360450745349365173⟩, ⟨2217787395183433782, 2217805666188025020⟩, true⟩

def words07 : List Nat := [360582925267553452, 360582930535545584, 360582934015836952, 360582934016048667, 360582933976390646, 360582931322367854, 360582928668598139, 360582927500091289, 360582922813010877, 360582914936146343]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 16770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 16700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360652334634941843, 360652336245376394⟩, ⟨(-1166125995467931644), (-1166107690919345122)⟩, true⟩

def words08 : List Nat := [360582907060172969, 360582901506808858, 360582897718331132, 360582894932410921, 360582892146807780, 360582886301108048, 360582882419955525, 360582882073885128, 360582883732296826, 360582887868810416]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 16780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 16700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360596373001467434, 360596374613924381⟩, ⟨(-226360356435357128), (-226342017920791930)⟩, true⟩

def words09 : List Nat := [360582889788261249, 360582891707506545, 360582893532685154, 360582897202717355, 360582899948246330, 360582902693484901, 360582902746506380, 360582902746718598, 360582901874516705, 360582902676663457]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 16790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 16700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 16700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk167B
