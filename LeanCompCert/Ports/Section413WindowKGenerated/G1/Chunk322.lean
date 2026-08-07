import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk322

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362445745837813349, 362445760290113644⟩, ⟨1262078846263817819, 1262393387378649247⟩, true⟩

def state01 : KState := ⟨⟨362453452176217477, 362453466637801906⟩, ⟨1014013471330519417, 1014328311441589755⟩, true⟩

def words00 : List Nat := [371284963836903086, 371284963262212948, 371284962207804607, 371284962114519280, 371284962020928072, 371284961871752164, 371284960439592085, 371284959269414791, 371284958098752029, 371284957737194691]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 32200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 32200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362448330145214773, 362448344616250506⟩, ⟨1179156454306241546, 1179471598891965536⟩, true⟩

def words01 : List Nat := [371284956760328375, 371284955785375487, 371284954810071126, 371284954795351239, 371284954521226381, 371284954317744540, 371284954113916404, 371284953913923887, 371284952566760867, 371284951431858575]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 32210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 32200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362414462842152371, 362414477322452408⟩, ⟨2270500159697085867, 2270815602826521353⟩, true⟩

def words02 : List Nat := [371284950296459067, 371284949561719877, 371284947545329837, 371284945468966414, 371284943392318682, 371284941600531293, 371284939392449047, 371284937564535497, 371284935736382804, 371284933903365425]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 32220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 32200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362471914410465429, 362471928900160218⟩, ⟨418559674584008211, 418875420552647887⟩, true⟩

def words03 : List Nat := [371284931718082693, 371284930395609183, 371284929072668397, 371284928709075282, 371284927208695950, 371284925472843738, 371284923736686819, 371284922959848457, 371284921715765153, 371284921313949072]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 32230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 32200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362440118903698526, 362440133402771570⟩, ⟨1443809214545614765, 1444125262917264879⟩, true⟩

def words04 : List Nat := [371284920911753488, 371284920310202820, 371284919016822935, 371284918436072392, 371284917854856805, 371284917570652898, 371284916263321689, 371284914951716234, 371284913639774267, 371284912480691486]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 32240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 32200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362430833413318315, 362430847921745964⟩, ⟨1743448048728170212, 1743764398832830572⟩, true⟩

def words05 : List Nat := [371284911092941679, 371284910663648396, 371284910234037107, 371284909786337335, 371284908059361957, 371284906629710238, 371284905199561365, 371284904727440757, 371284903049353609, 371284901374902593]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 32250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 32200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362456965581801026, 362456980099544548⟩, ⟨900350200078616209, 900666850761183483⟩, true⟩

def words06 : List Nat := [371284899700103834, 371284898983233847, 371284897913141139, 371284896930892509, 371284895948379974, 371284894795394469, 371284893016315638, 371284891961645424, 371284890906515630, 371284890445090293]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 32260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 32200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362450472916382656, 362450487443607292⟩, ⟨1109997690129043234, 1110314646815571522⟩, true⟩

def words07 : List Nat := [371284889580994918, 371284888700073055, 371284887818770262, 371284887700508773, 371284887257006826, 371284887097284761, 371284886937245876, 371284886543524845, 371284884872429771, 371284883808130699]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 32270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 32200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362418359458813099, 362418373995300103⟩, ⟨2146810239634957485, 2147127495360011861⟩, true⟩

def words08 : List Nat := [371284882743308865, 371284882390967357, 371284880761681070, 371284879008291553, 371284877254607975, 371284875512298842, 371284873289642803, 371284871926972433, 371284870564021688, 371284869117485301]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 32280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 32200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362465830366888395, 362465844912793108⟩, ⟨613651596894984316, 613969156763908898⟩, true⟩

def words09 : List Nat := [371284867058958050, 371284865402436597, 371284863745471392, 371284862877222740, 371284860880607450, 371284858727404840, 371284856573896353, 371284855376111689, 371284853833165445, 371284853245819855]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 32290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 32200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 32200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk322
