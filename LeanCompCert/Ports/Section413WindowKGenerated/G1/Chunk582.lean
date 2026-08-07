import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk582

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362510899997962540, 362510949542167070⟩, ⟨(-1512868569088408222), (-1510920774272496404)⟩, true⟩

def state01 : KState := ⟨⟨362488473357003662, 362488522918696013⟩, ⟨(-207559777657212999), (-205610964958779081)⟩, true⟩

def words00 : List Nat := [371284989650376894, 371284989757526626, 371284989826152404, 371284989895405927, 371284989980987212, 371284989983153122, 371284990187920221, 371284990439549792, 371284990689124001, 371284990751838224]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 58200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 58200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362515667741072300, 362515717320545717⟩, ⟨(-1790645274094877052), (-1788695426275074736)⟩, true⟩

def words01 : List Nat := [371284991109326385, 371284991467880100, 371284992035017447, 371284992321315752, 371284992562228002, 371284992803765387, 371284993339902653, 371284993748639373, 371284994277711594, 371284994807598927]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 58210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 58200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362501480761595346, 362501530358817545⟩, ⟨(-964689052368285975), (-962738171121948449)⟩, true⟩

def words02 : List Nat := [371284995337833827, 371284995526546733, 371284995823339512, 371284996121157126, 371284996431734009, 371284996498532432, 371284996562393129, 371284996626890070, 371284996985935710, 371284997272126231]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 58220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 58200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500019515239022, 362500069130217715⟩, ⟨(-879524734787515034), (-877572819494670722)⟩, true⟩

def words03 : List Nat := [371284997852699921, 371284998434072150, 371284998936404519, 371284999176006858, 371284999482283471, 371284999789499942, 371285000390984836, 371285000653093906, 371285000913310177, 371285001174319042]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 58230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 58200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362505774995368917, 362505824627929946⟩, ⟨(-1214669596243557467), (-1212716656864116049)⟩, true⟩

def words04 : List Nat := [371285001699757230, 371285002103735319, 371285002802081277, 371285003501184904, 371285004104229283, 371285004314592160, 371285004612601049, 371285004911633890, 371285005455816529, 371285005815259535]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 58240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 58200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362500164955841211, 362500214606304219⟩, ⟨(-887795645080633543), (-885841662818583307)⟩, true⟩

def words05 : List Nat := [371285006172744097, 371285006530862043, 371285007082584323, 371285007562353861, 371285008111484266, 371285008661388429, 371285009211756604, 371285009369661814, 371285009631991685, 371285009895385791]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 58250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 58200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474240019138870, 362474289687142813⟩, ⟨622699213935784564, 624654218224565462⟩, true⟩

def words06 : List Nat := [371285010179110728, 371285010181078404, 371285010072025260, 371285009962274235, 371285009851757461, 371285009811415611, 371285009671040772, 371285009677530637, 371285009681986463, 371285009684023276]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 58260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 58200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495284173321982, 362495333859129925⟩, ⟨(-603634501364684690), (-601678459548273226)⟩, true⟩

def words07 : List Nat := [371285009612342219, 371285009725672693, 371285010053948025, 371285010055915970, 371285009991701866, 371285009835697257, 371285009766556741, 371285009768739822, 371285009930002676, 371285010109373602]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 58270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 58200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482436887098012, 362482486590672758⟩, ⟨145190474764981754, 147147552122562948⟩, true⟩

def words08 : List Nat := [371285010286692605, 371285010288698067, 371285010512235855, 371285010754313587, 371285011083924232, 371285011085892748, 371285011055314979, 371285011024184579, 371285010993162489, 371285010995409807]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 58280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 58200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468546705339901, 362468596426629067⟩, ⟨954983157810520089, 956941267829191235⟩, true⟩

def words09 : List Nat := [371285011162258866, 371285011373204928, 371285011542374302, 371285011544343258, 371285011320997869, 371285011158279303, 371285011069787795, 371285011071757006, 371285010792895287, 371285010513555812]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 58290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 58200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 58200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk582
