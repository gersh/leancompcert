import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk031

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362507015976909022, 362507016084742462⟩, ⟨(-57836223197971940), (-57835996368252762)⟩, true⟩

def state01 : KState := ⟨⟨362584631009835660, 362584631118401317⟩, ⟨(-298375117068115246), (-298374887964789302)⟩, true⟩

def words00 : List Nat := [371288414717515346, 371288433826231748, 371288524183967951, 371288614483536465, 371288679999244497, 371288679999326252, 371288608576410787, 371288601812011929, 371288690639871375, 371288721479068373]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 3100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 3100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362435307205300663, 362435307314613501⟩, ⟨166715324500896246, 166715555931721104⟩, true⟩

def words01 : List Nat := [371288734103596613, 371288746720041917, 371288811719069946, 371288828117620734, 371288844538856331, 371288860949584991, 371288877858819384, 371288877858901552, 371288758919490703, 371288741787668540]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 3110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 3100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362374027667655663, 362374027777701702⟩, ⟨359690587238452598, 359690820960721330⟩, true⟩

def words02 : List Nat := [371288809223545675, 371288810724737289, 371288810724799388, 371288809010353391, 371288836863512077, 371288836863602555, 371288866807357254, 371288918008212968, 371288944972811585, 371288944972896821]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 3120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 3100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362712956375822605, 362712956486614319⟩, ⟨(-703063070070585368), (-703062834010590554)⟩, true⟩

def words03 : List Nat := [371288946152254342, 371288984010503798, 371289086051524485, 371289086051607068, 371289053580800893, 371288997428182509, 371288985812861828, 371288985812952726, 371289051125372616, 371289122410202161]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 3130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 3100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362380204549787945, 362380204661328547⟩, ⟨342020428208478530, 342020666623853482⟩, true⟩

def words04 : List Nat := [371289191264881875, 371289191264964730, 371289126334400624, 371289103351192133, 371289080382558697, 371289056328954413, 371288969222157778, 371288882374891509, 371288795582751412, 371288782650732945]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 3140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 3100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361948972767995665, 361948972880284106⟩, ⟨1704380026100847928, 1704380266875816450⟩, true⟩

def words05 : List Nat := [371288780071602167, 371288811930548012, 371288844255490797, 371288844255574050, 371288780074450046, 371288746133501840, 371288712214015666, 371288674445476851, 371288504461980667, 371288333724232150]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 3150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 3100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362326455452920582, 362326455565956033⟩, ⟨510357681559166548, 510357924698486930⟩, true⟩

def words06 : List Nat := [371288163094474344, 371288063345608219, 371287927776838133, 371287890903179130, 371287854052794591, 371287800018386347, 371287614418510904, 371287527356551947, 371287451756626261, 371287451756712654]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 3160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 3100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362239066788027985, 362239066901825321⟩, ⟨788281666818651820, 788281912377067736⟩, true⟩

def words07 : List Nat := [371287400985350666, 371287327657723470, 371287254376282958, 371287248711097286, 371287200962838625, 371287179692618748, 371287158435760955, 371287135293041808, 371287032272083933, 371286954295654588]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 3170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 3100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362303488370340559, 362303488484885252⟩, ⟨583333550679656866, 583333798618596564⟩, true⟩

def words08 : List Nat := [371286896223188563, 371286896223272609, 371286813779118350, 371286731563398901, 371286649399274734, 371286568770398370, 371286441295738893, 371286411321749382, 371286381366530885, 371286351744640298]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 3180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 3100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362622761177831395, 362622761293139151⟩, ⟨(-436062985730422097), (-436062735353524175)⟩, true⟩

def words09 : List Nat := [371286334330496843, 371286374197353390, 371286488618550089, 371286488618634361, 371286473572143930, 371286442517590040, 371286446874535863, 371286449090623717, 371286491688245412, 371286534259289253]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 3190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 3100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 3100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk031
