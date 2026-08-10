import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk203A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk203B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk203A

def state06 : KState := ⟨⟨360668217191436348, 360668219601335598⟩, ⟨(-1753484835997476753), (-1753451632041235543)⟩, true⟩

def words05 : List Nat := [360582092791250188, 360582092906592690, 360582095425098320, 360582095537259647, 360582095537500671, 360582093278548255, 360582091163393203, 360582092991883023, 360582097222281442, 360582101452323210]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 20350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 20300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360624334574523754, 360624336986912760⟩, ⟨(-860488823574979951), (-860455568915031731)⟩, true⟩

def words06 : List Nat := [360582103839135413, 360582103839396653, 360582103821224876, 360582103747539699, 360582103673792926, 360582102991772480, 360582101604567062, 360582098827099454, 360582096049854143, 360582097746378912]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 20360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 20300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360501882682390720, 360501885097239402⟩, ⟨1634648378514968306, 1634681683291076172⟩, true⟩

def words07 : List Nat := [360582100509043584, 360582103271487712, 360582104828837446, 360582104921255945, 360582104921475011, 360582104236545180, 360582103551607409, 360582101857726624, 360582099125296634, 360582095189648189]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 20370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 20300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360509795563337330, 360509797980654120⟩, ⟨1473341787562800694, 1473375142651092468⟩, true⟩

def words08 : List Nat := [360582091254327041, 360582088970565267, 360582088175039896, 360582086525938976, 360582084876976041, 360582081135308703, 360582074995687963, 360582068422721074, 360582061850322637, 360582057673770898]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 20380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 20300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360581191195400012, 360581193615212221⟩, ⟨17029758489459698, 17063164471714242⟩, true⟩

def words09 : List Nat := [360582054130302665, 360582048709334133, 360582043288847295, 360582040263566892, 360582039166294832, 360582037463258613, 360582035760361909, 360582032519966475, 360582030085547455, 360582030044843188]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 20390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 20300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 20300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk203B
