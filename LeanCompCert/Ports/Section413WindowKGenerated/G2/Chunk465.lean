import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk465

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583166446724785, 360583179930864685⟩, ⟨(-9351994010004352), (-8928288953876336)⟩, true⟩

def state01 : KState := ⟨⟨360557613641129867, 360557627131284503⟩, ⟨1178824931821705698, 1179248916593418004⟩, true⟩

def words00 : List Nat := [360582987929307241, 360582987706793382, 360582987022739960, 360582986105208194, 360582985187611874, 360582984065807247, 360582983247456652, 360582982890448889, 360582982533371690, 360582981870407131]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 46500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 46500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360600827756590434, 360600841252769198⟩, ⟨(-831246286267237148), (-830822021283259234)⟩, true⟩

def words01 : List Nat := [360582981325788923, 360582981242516187, 360582981441809744, 360582981590391997, 360582981590990640, 360582981303126630, 360582981095899982, 360582981408916195, 360582981793353370, 360582982177915192]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 46510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 46500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587932819351976, 360587946321625204⟩, ⟨(-231319735514887468), (-230895186987252806)⟩, true⟩

def words02 : List Nat := [360582982331708375, 360582982501953545, 360582983132896783, 360582983764000061, 360582984273775126, 360582984506588152, 360582984507159571, 360582984446181727, 360582984385095295, 360582984141852854]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 46520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 46500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360536555443678092, 360536568951959222⟩, ⟨2159565359010051132, 2159990187115978094⟩, true⟩

def words03 : List Nat := [360582984252830233, 360582984363923640, 360582984364492465, 360582984245070868, 360582983820936975, 360582983157062527, 360582982493017351, 360582982190136166, 360582981426576341, 360582980429980623]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 46530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 46500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580090118104047, 360580103632422575⟩, ⟨133080270306748966, 133505379421992662⟩, true⟩

def words04 : List Nat := [360582979433283456, 360582978508550987, 360582977814903310, 360582977012286564, 360582976209655014, 360582975007115885, 360582973790693732, 360582972917720388, 360582972044590198, 360582971631980513]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 46540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 46500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360561839565070236, 360561853085467657⟩, ⟨982716189522564010, 983141581641145962⟩, true⟩

def words05 : List Nat := [360582971570939932, 360582971223294603, 360582970875539176, 360582970682310462, 360582970682845231, 360582970585492726, 360582970488089752, 360582970035232337, 360582969122060360, 360582968669265792]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 46550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 46500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360562909925966906, 360562923452382973⟩, ⟨932835465947922128, 933261138324750944⟩, true⟩

def words06 : List Nat := [360582968216278857, 360582968103341282, 360582967721351832, 360582966931293868, 360582966141154710, 360582965155614639, 360582964451735619, 360582964207981080, 360582963964168666, 360582963416701736]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 46560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 46500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606710462229115, 360606723994689058⟩, ⟨(-1107231449508185258), (-1106805495638984180)⟩, true⟩

def words07 : List Nat := [360582962986917589, 360582962545509033, 360582962121713202, 360582962266578371, 360582962267175310, 360582961981970431, 360582961719508392, 360582962094460760, 360582962605111054, 360582963115883559]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 46570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 46500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573481727195542, 360573495265736354⟩, ⟨440514955689368958, 440941192836527926⟩, true⟩

def words08 : List Nat := [360582963396627237, 360582963397266596, 360582963302059960, 360582963386647658, 360582963387195644, 360582963052123197, 360582962257268403, 360582961202996837, 360582960148646778, 360582959554056520]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 46580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 46500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360536740272942771, 360536753817514646⟩, ⟨2152602193776476020, 2153028711941213850⟩, true⟩

def words09 : List Nat := [360582959607794046, 360582959864792636, 360582959865367997, 360582959854036272, 360582959382967268, 360582958795779630, 360582958208426482, 360582957777995064, 360582957141213900, 360582956150388921]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 46590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 46500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 46500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk465
