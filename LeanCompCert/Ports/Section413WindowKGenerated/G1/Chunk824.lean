import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk824

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362501568311772704, 362501670356599428⟩, ⟨(-1356926995236302529), (-1351249275964582779)⟩, true⟩

def state01 : KState := ⟨⟨362484989418851816, 362485091489433461⟩, ⟨9206296837770556, 14886138444535084⟩, true⟩

def words00 : List Nat := [371285272065002575, 371285272067857896, 371285272112554015, 371285272191616561, 371285272314281211, 371285272317136609, 371285272243632191, 371285272169303525, 371285272121271971, 371285272124531684]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479974918543374, 362480077014852911⟩, ⟨422479266202722818, 428161228174122676⟩, true⟩

def words01 : List Nat := [371285272172446858, 371285272223675810, 371285272273826244, 371285272276682383, 371285272148303558, 371285272056279294, 371285272001303371, 371285272004212635, 371285271945204770, 371285271885371889]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485170325107747, 362485272446942749⟩, ⟨(-5718580717997272), (-34514804847548)⟩, true⟩

def words02 : List Nat := [371285271908548527, 371285271939202147, 371285272018465993, 371285272098902374, 371285272137247072, 371285272140103286, 371285271981914474, 371285271957352751, 371285272025269198, 371285272028231284]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479735728312434, 362479837876273144⟩, ⟨442305022530146649, 447991242111564461⟩, true⟩

def words03 : List Nat := [371285272030389819, 371285272024747030, 371285272068672652, 371285272071842096, 371285272116386466, 371285272163239286, 371285272208899899, 371285272211757532, 371285272087573682, 371285272025255575]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473324488612495, 362473426662024049⟩, ⟨970878037365982109, 976566355247896345⟩, true⟩

def words04 : List Nat := [371285272003749059, 371285272006605863, 371285271855076566, 371285271704254808, 371285271552381920, 371285271408290850, 371285271224385837, 371285271152782157, 371285271080197974, 371285271008358166]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk824
