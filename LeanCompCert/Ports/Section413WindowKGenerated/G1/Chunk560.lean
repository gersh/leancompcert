import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk560

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496544903597938, 362496590632453006⟩, ⟨(-654389120975458652), (-652659212157127280)⟩, true⟩

def state01 : KState := ⟨⟨362478273617126324, 362478319362961931⟩, ⟨368823870252615423, 370554730070521741⟩, true⟩

def words00 : List Nat := [371284936361422484, 371284936363307607, 371284936130061323, 371284936174327846, 371284936256099029, 371284936257985163, 371284935972034687, 371284935618837884, 371284935264870935, 371284935230308308]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 56000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 56000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362469282484021141, 362469328246826023⟩, ⟨872556564457694656, 874288374811170664⟩, true⟩

def words01 : List Nat := [371284935280907902, 371284935450386238, 371284935619235206, 371284935621153698, 371284935525343671, 371284935463680751, 371284935503491295, 371284935505378145, 371284935241902145, 371284934965405302]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 56010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 56000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473767141308175, 362473812921010534⟩, ⟨621284667223900484, 623017424258481250⟩, true⟩

def words02 : List Nat := [371284934688120758, 371284934505116283, 371284934162190211, 371284933981655625, 371284933800540483, 371284933575786497, 371284932966439551, 371284932648910787, 371284932330393816, 371284932275361034]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 56020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 56000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477796539279278, 362477842336174906⟩, ⟨395519029435623221, 397252749896793961⟩, true⟩

def words03 : List Nat := [371284932078324459, 371284931868632105, 371284931728645575, 371284931730757826, 371284931695401599, 371284931677033015, 371284931658045891, 371284931639465004, 371284931196040921, 371284931071897547]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 56030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 56000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362471933740450452, 362471979554173651⟩, ⟨724172321144636677, 725906984710101337⟩, true⟩

def words04 : List Nat := [371284931138378789, 371284931140298422, 371284931069213626, 371284930999257051, 371284930928607125, 371284930871041856, 371284930673517566, 371284930695443752, 371284930696883140, 371284930615453047]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 56040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 56000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362493208648210020, 362493254478973200⟩, ⟨(-468390280496634349), (-466654661755911227)⟩, true⟩

def words05 : List Nat := [371284930385676769, 371284930385673474, 371284930700474956, 371284930702362094, 371284930595592338, 371284930400480920, 371284930244188878, 371284930246268399, 371284930276697511, 371284930427283864]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 56050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 56000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362465286501269439, 362465332349104265⟩, ⟨1097020382373655313, 1098756958235692813⟩, true⟩

def words06 : List Nat := [371284930577182423, 371284930579069855, 371284930304977727, 371284930163662838, 371284930021392606, 371284929976507371, 371284929622186726, 371284929209461011, 371284928796008788, 371284928513866807]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 56060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 56000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362458912053048031, 362458957917873541⟩, ⟨1454545853130790742, 1456283381748436038⟩, true⟩

def words07 : List Nat := [371284928165659613, 371284928086737656, 371284928007164551, 371284927928054821, 371284927539042566, 371284927245529667, 371284926951092765, 371284926789071490, 371284926342086540, 371284925881171481]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 56070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 56000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476567896235287, 362476613777962403⟩, ⟨464385635231499782, 466124111776708556⟩, true⟩

def words08 : List Nat := [371284925419408525, 371284925276150212, 371284925015002274, 371284924952363659, 371284924889122052, 371284924776333860, 371284924319595805, 371284924181516151, 371284924065039025, 371284924066993901]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 56080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 56000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486769640949101, 362486815539887855⟩, ⟨(-107893835366519020), (-106154393334477496)⟩, true⟩

def words09 : List Nat := [371284923920273191, 371284923710107195, 371284923604568662, 371284923606649518, 371284923560173107, 371284923567823844, 371284923569251207, 371284923551158396, 371284923302370913, 371284923338441634]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 56090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 56000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 56000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk560
