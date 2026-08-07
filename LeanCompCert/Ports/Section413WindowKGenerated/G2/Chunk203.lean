import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk203

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360610711585925980, 360610713981019637⟩, ⟨(-578617448227397850), (-578584545268488460)⟩, true⟩

def state01 : KState := ⟨⟨360585801718825557, 360585804116398409⟩, ⟨(-73269638031689340), (-73236684732879954)⟩, true⟩

def words00 : List Nat := [360582213683469858, 360582213492639501, 360582210884723518, 360582209953304618, 360582209021906073, 360582206946561920, 360582205904069369, 360582202963942530, 360582200024055802, 360582198351801251]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 20300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 20300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360470005817736009, 360470008217762367⟩, ⟨2279400846083722758, 2279433849225908280⟩, true⟩

def words01 : List Nat := [360582199570183986, 360582200788496117, 360582200788730562, 360582200294087433, 360582199907826568, 360582198010824930, 360582196113935410, 360582194564378027, 360582190600937912, 360582185080421123]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 20310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 20300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360550342476201055, 360550344878691678⟩, ⟨646449860873324593, 646482914101707199⟩, true⟩

def words02 : List Nat := [360582179560392482, 360582173983428101, 360582169606293890, 360582167639436372, 360582165672752222, 360582161636512246, 360582155188035177, 360582151149361357, 360582147111002289, 360582144333394173]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 20320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 20300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360485961666529270, 360485964071505153⟩, ⟨1955864996136743540, 1955898099902617500⟩, true⟩

def words03 : List Nat := [360582142769541798, 360582139919383963, 360582137069454443, 360582137419311732, 360582137419533904, 360582136517270836, 360582135615067700, 360582133503059354, 360582128980979800, 360582124253407937]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 20330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 20300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360552698915224777, 360552701322661574⟩, ⟨598110277398276230, 598143431231432266⟩, true⟩

def words04 : List Nat := [360582119526212246, 360582117205374367, 360582114990751244, 360582111567699864, 360582108144943514, 360582103351160616, 360582099788840211, 360582098631582489, 360582097474417181, 360582094120265085]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 20340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 20300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk203
