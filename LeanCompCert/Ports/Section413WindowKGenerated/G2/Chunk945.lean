import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk945

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360595554683936442, 360595613607471687⟩, ⟨(-1280694691781687327), (-1276934676150755221)⟩, true⟩

def state01 : KState := ⟨⟨360576090006206129, 360576148942625925⟩, ⟨558758758959766448, 562519992246264298⟩, true⟩

def words00 : List Nat := [360582101356254367, 360582101386990767, 360582101388213591, 360582101341734948, 360582101295034314, 360582101196186905, 360582101166099835, 360582101097794234, 360582101029351998, 360582100905299148]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 94500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 94500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607001535774862, 360607060485112554⟩, ⟨(-2362858525328831432), (-2359096071108192314)⟩, true⟩

def words01 : List Nat := [360582100843430271, 360582100842455025, 360582100950472092, 360582101096027652, 360582101146564326, 360582101197206624, 360582101323612836, 360582101521199092, 360582101786366702, 360582102051842612]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 94510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 94500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589056306027151, 360589115268419846⟩, ⟨(-666725132321955252), (-662961444078613800)⟩, true⟩

def words02 : List Nat := [360582102230956283, 360582102320168702, 360582102374614337, 360582102429448301, 360582102430630851, 360582102432000218, 360582102346258151, 360582102203529401, 360582102060517163, 360582102104017919]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 94520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 94500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567953764705241, 360568012739988632⟩, ⟨1328284935137419612, 1332049842002428178⟩, true⟩

def words03 : List Nat := [360582102291172885, 360582102478586585, 360582102609648650, 360582102723203506, 360582102741281260, 360582102759722767, 360582102779458295, 360582102780827858, 360582102689193064, 360582102541575288]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 94530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 94500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592258795483966, 360592317783712096⟩, ⟨(-969571372003034279), (-965805241279200351)⟩, true⟩

def words04 : List Nat := [360582102393648424, 360582102407722336, 360582102570394750, 360582102733329424, 360582102786588960, 360582102787959180, 360582102872947746, 360582102972309137, 360582103025640895, 360582103135096226]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 94540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 94500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360590872540542268, 360590931541807871⟩, ⟨(-838496901186485014), (-834729537705314452)⟩, true⟩

def words05 : List Nat := [360582103188174683, 360582103241402086, 360582103347272101, 360582103536116859, 360582103696237185, 360582103856611190, 360582103950825803, 360582103952195611, 360582104028213579, 360582104123128867]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 94550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 94500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594983163439611, 360595042177620031⟩, ⟨(-1227222771364651894), (-1223454186593054098)⟩, true⟩

def words06 : List Nat := [360582104329382020, 360582104502607075, 360582104586639289, 360582104670784054, 360582104726378131, 360582104837939105, 360582104965946497, 360582105094206414, 360582105154006927, 360582105292247211]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 94560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 94500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602971458748124, 360603030485856324⟩, ⟨(-1982745660924003961), (-1978975853509099717)⟩, true⟩

def words07 : List Nat := [360582105468148244, 360582105644460276, 360582105932115704, 360582106108633006, 360582106182767389, 360582106257001287, 360582106300958000, 360582106431971404, 360582106654309949, 360582106876954863]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 94570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 94500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595072982400651, 360595132022570121⟩, ⟨(-1235708823454398239), (-1231937780641111819)⟩, true⟩

def words08 : List Nat := [360582107038155083, 360582107163870987, 360582107401061689, 360582107638676281, 360582107847586833, 360582107945342176, 360582107973306926, 360582108001430656, 360582108046146782, 360582108185411818]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 94580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 94500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583853883419247, 360583912936500211⟩, ⟨(-174466827102265135), (-170694562925967721)⟩, true⟩

def words09 : List Nat := [360582108321603983, 360582108458036713, 360582108538180940, 360582108539551159, 360582108508259293, 360582108449043774, 360582108440408191, 360582108532489992, 360582108552797855, 360582108573301874]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 94590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 94500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 94500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk945
