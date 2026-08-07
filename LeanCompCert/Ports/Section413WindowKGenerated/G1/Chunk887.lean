import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk887

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483832504038124, 362483951422936292⟩, ⟨100193646175222396, 107315646412043020⟩, true⟩

def state01 : KState := ⟨⟨362476967988228579, 362477086935032427⟩, ⟨709072258902142727, 716196734507033697⟩, true⟩

def words00 : List Nat := [371285161283607103, 371285161273011899, 371285161092112311, 371285161027833171, 371285160961852514, 371285160932095010, 371285160771484849, 371285160611857506, 371285160451003143, 371285160396136103]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 88700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 88700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362463699811704943, 362463818786398805⟩, ⟨1886149621914563241, 1893276571788627057⟩, true⟩

def words01 : List Nat := [371285160307270409, 371285160222151177, 371285160135967230, 371285160051165024, 371285159796199695, 371285159549140372, 371285159300516344, 371285159168873953, 371285158930672640, 371285158693655215]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 88710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 88700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483359622564192, 362483478624928816⟩, ⟨141844800920549943, 148974205885114773⟩, true⟩

def words02 : List Nat := [371285158455223686, 371285158345011708, 371285158181305327, 371285158095293972, 371285158008404404, 371285157902651992, 371285157703827061, 371285157622949569, 371285157582679256, 371285157585887738]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 88720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 88700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483752496099385, 362483871526683573⟩, ⟨107013918928125803, 114145827953102367⟩, true⟩

def words03 : List Nat := [371285157569298970, 371285157554391261, 371285157631137604, 371285157674500012, 371285157755447722, 371285157837624502, 371285157894365243, 371285157897472900, 371285157832440771, 371285157821792353]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 88730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 88700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483697885594725, 362483816943700957⟩, ⟨111873577324720151, 119007928801079289⟩, true⟩

def words04 : List Nat := [371285157921703986, 371285157924796851, 371285157870263594, 371285157816779494, 371285157762083691, 371285157747517616, 371285157747657467, 371285157813420580, 371285157874903394, 371285157878109984]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 88740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 88700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481917001688549, 362482036087825384⟩, ⟨269942890387318842, 277079729719888082⟩, true⟩

def words05 : List Nat := [371285157934370583, 371285158007376709, 371285158120663124, 371285158123756426, 371285158079731053, 371285158002444174, 371285157923936352, 371285157890903219, 371285157792816076, 371285157761211143]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362467002592440000, 362467121706472732⟩, ⟨1593783973553722867, 1600923289067101435⟩, true⟩

def words06 : List Nat := [371285157728353858, 371285157696277191, 371285157494135002, 371285157393318518, 371285157290990488, 371285157208461073, 371285156956158652, 371285156677656479, 371285156397850449, 371285156214629397]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362464865535547483, 362464984677391608⟩, ⟨1783567153375145804, 1790708937846244014⟩, true⟩

def words07 : List Nat := [371285156013569725, 371285155940454670, 371285155866324082, 371285155787205905, 371285155625803874, 371285155491659911, 371285155355857163, 371285155305403969, 371285155085160519, 371285154861417811]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468953442459643, 362469072612032533⟩, ⟨1420604790657793400, 1427749037030288014⟩, true⟩

def words08 : List Nat := [371285154636377028, 371285154427756344, 371285154154460301, 371285153990258362, 371285153825075393, 371285153639050291, 371285153296117734, 371285153048495414, 371285152799241673, 371285152677772260]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471461553675792, 362471580751460496⟩, ⟨1197897771912476224, 1205044523349918602⟩, true⟩

def words09 : List Nat := [371285152498991521, 371285152306261602, 371285152112225210, 371285152046187283, 371285151915267330, 371285151776915133, 371285151637548076, 371285151498963046, 371285151221601600, 371285151072669392]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk887
