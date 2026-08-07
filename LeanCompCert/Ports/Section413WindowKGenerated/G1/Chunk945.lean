import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk945

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493330032113822, 362493465674110134⟩, ⟨(-792110775527642464), (-783456384589581748)⟩, true⟩

def state01 : KState := ⟨⟨362478030697935706, 362478166369377492⟩, ⟨653746493572005630, 662403667263499914⟩, true⟩

def words00 : List Nat := [371285175357088600, 371285175360398974, 371285175350356546, 371285175328754958, 371285175305856452, 371285175302336081, 371285175253990047, 371285175233027076, 371285175210998973, 371285175190319864]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 94500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 94500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500178146272280, 362500313847672519⟩, ⟨(-1439516422863496464), (-1430856417650471708)⟩, true⟩

def words01 : List Nat := [371285175126945929, 371285175139518657, 371285175262332036, 371285175305971209, 371285175331585822, 371285175358201669, 371285175477449631, 371285175547590272, 371285175709996580, 371285175873913773]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 94510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 94500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486249100088115, 362486384831393520⟩, ⟨(-122933941561199889), (-114271109559974305)⟩, true⟩

def words02 : List Nat := [371285176014717237, 371285176019638074, 371285176058678720, 371285176099374500, 371285176166704477, 371285176170015881, 371285176098888882, 371285176028072608, 371285175993276208, 371285176009847573]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 94520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 94500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477855548473327, 362477991309546278⟩, ⟨670612732653341528, 679278378732772538⟩, true⟩

def words03 : List Nat := [371285176136874789, 371285176265218087, 371285176392117713, 371285176419833336, 371285176441906273, 371285176465662114, 371285176541409533, 371285176544721431, 371285176471538361, 371285176399230357]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 94530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 94500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488004816991607, 362488140607739794⟩, ⟨(-288893807421595038), (-280225355693215174)⟩, true⟩

def words04 : List Nat := [371285176361448088, 371285176365161887, 371285176470026609, 371285176580963286, 371285176660737289, 371285176664050950, 371285176672436711, 371285176735414947, 371285176824761258, 371285176859543655]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 94540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 94500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490737290098563, 362490873111060926⟩, ⟨(-547254248624377270), (-538582939997222928)⟩, true⟩

def words05 : List Nat := [371285176893018465, 371285176927642644, 371285177041297171, 371285177111774755, 371285177214661047, 371285177318871798, 371285177418742604, 371285177422055198, 371285177432836969, 371285177497224385]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 94550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 94500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487675426494685, 362487811276976846⟩, ⟨(-257684202957313039), (-249010102783066691)⟩, true⟩

def words06 : List Nat := [371285177671630516, 371285177740162214, 371285177789329478, 371285177839513741, 371285177922238911, 371285177950549787, 371285178034230631, 371285178119273262, 371285178196370944, 371285178227703993]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 94560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 94500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497669814226022, 362497805694610474⟩, ⟨(-1202904980435916927), (-1194228052250865757)⟩, true⟩

def words07 : List Nat := [371285178328291554, 371285178430593438, 371285178643071402, 371285178707570035, 371285178753474453, 371285178800443592, 371285178874787195, 371285178910506000, 371285179046255940, 371285179183448075]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 94570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 94500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489262226022657, 362489398136328634⟩, ⟨(-407676490634145607), (-398996732320765613)⟩, true⟩

def words08 : List Nat := [371285179324312199, 371285179356390745, 371285179499270789, 371285179643966325, 371285179820693256, 371285179849400081, 371285179867767531, 371285179887250564, 371285179962174282, 371285180010583894]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 94580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 94500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485502711989718, 362485638652179791⟩, ⟨(-52041724992081500), (-43359139789973376)⟩, true⟩

def words09 : List Nat := [371285180103815946, 371285180198404160, 371285180291464318, 371285180294777829, 371285180238709904, 371285180218031616, 371285180282897448, 371285180299188262, 371285180306536569, 371285180315166547]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 94590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 94500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 94500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk945
