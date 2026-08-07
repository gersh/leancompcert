import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk328

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362472488735335292, 362472503754183265⟩, ⟨400551146272475023, 400884100817044197⟩, true⟩

def state01 : KState := ⟨⟨362506204856529249, 362506219884861162⟩, ⟨(-705327242534425502), (-704993976868245366)⟩, true⟩

def words00 : List Nat := [371284726013703988, 371284726330385552, 371284727574299334, 371284728818557664, 371284729914937757, 371284729956048797, 371284730787741293, 371284731619939199, 371284732715921055, 371284733371896966]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 32800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 32800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497251482579268, 362497266520549046⟩, ⟨(-411507121274738708), (-411173539340488078)⟩, true⟩

def words01 : List Nat := [371284734027981301, 371284734684378270, 371284735613416206, 371284736079684540, 371284736829658721, 371284737580025628, 371284738330664518, 371284738331724077, 371284738379721267, 371284738762731171]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 32810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 32800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467613320502892, 362467628367920565⟩, ⟨561351976850448859, 561685868913617607⟩, true⟩

def words02 : List Nat := [371284739792932617, 371284739793992166, 371284739588306550, 371284739195950222, 371284738803200411, 371284738521880396, 371284737776597221, 371284737615231342, 371284737453527567, 371284737288691617]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 32820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 32800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362511834952311661, 362511850009317219⟩, ⟨(-890636491281073521), (-890302284400528763)⟩, true⟩

def words03 : List Nat := [371284737173225290, 371284737579433875, 371284738911007023, 371284739007757877, 371284739008583774, 371284738871317010, 371284738979680981, 371284738980853889, 371284739707130925, 371284740533832291]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 32830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 32800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362500414240822796, 362500429307402983⟩, ⟨(-515642897165386935), (-515308375805916425)⟩, true⟩

def words04 : List Nat := [371284741260753169, 371284741261813272, 371284741171123835, 371284741589359235, 371284742291422372, 371284742292489858, 371284742164437980, 371284742037887282, 371284742597633564, 371284743076365696]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 32840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 32800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362454313843370634, 362454328919494972⟩, ⟨999021021074891774, 999355856008583146⟩, true⟩

def words05 : List Nat := [371284743698108182, 371284744320216730, 371284744885333711, 371284744886394286, 371284744217898776, 371284743834526615, 371284743450625439, 371284743298082081, 371284742377517558, 371284741453153176]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 32850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 32800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472369868897300, 362472384954519696⟩, ⟨405634752378042573, 405969899465927063⟩, true⟩

def words06 : List Nat := [371284740528385053, 371284740187311545, 371284739383214584, 371284739310757136, 371284739237968205, 371284738948626398, 371284737426424360, 371284736552338030, 371284735726144049, 371284735727244550]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 32860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 32800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362462615653183202, 362462630748493126⟩, ⟨726429319362252512, 726764784928906920⟩, true⟩

def words07 : List Nat := [371284735352303588, 371284734979080656, 371284735037589505, 371284735038758346, 371284735236953597, 371284735465894677, 371284735688472745, 371284735689536976, 371284734971287933, 371284734300346195]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 32870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 32800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475961251808625, 362475976356576164⟩, ⟨287541371692465488, 287877148273689504⟩, true⟩

def words08 : List Nat := [371284733772605027, 371284733773666969, 371284732858985686, 371284731881705323, 371284730904088319, 371284730211698151, 371284729249032663, 371284729209476479, 371284729169557432, 371284729082276185]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 32880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 32800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362498211187812600, 362498226302172168⟩, ⟨(-444411191314713649), (-444075099202936753)⟩, true⟩

def words09 : List Nat := [371284729321671803, 371284729827686391, 371284730549075104, 371284730550137188, 371284730041183999, 371284729297095810, 371284728589855642, 371284728591025411, 371284728577587481, 371284728989044819]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 32890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 32800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 32800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk328
