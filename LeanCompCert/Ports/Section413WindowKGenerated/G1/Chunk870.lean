import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk870

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479862341604641, 362479976575421199⟩, ⟨447429447205600396, 454139848725125638⟩, true⟩

def state01 : KState := ⟨⟨362477028306655314, 362477142567483180⟩, ⟨693993292802674459, 700706044446597309⟩, true⟩

def words00 : List Nat := [371285196548220359, 371285196551249278, 371285196432449217, 371285196287270037, 371285196140961512, 371285196036308705, 371285195875800921, 371285195835298716, 371285195793746119, 371285195734296726]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 87000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 87000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492550081808830, 362492664369918277⟩, ⟨(-656614573249037832), (-649899447693723038)⟩, true⟩

def words01 : List Nat := [371285195683194681, 371285195726216508, 371285195899612237, 371285195910134022, 371285195912477341, 371285195901928306, 371285195919865233, 371285195923202590, 371285195974814294, 371285196064018624]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 87010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 87000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481129464425833, 362481243779898871⟩, ⟨337229821573606229, 343947328443658851⟩, true⟩

def words02 : List Nat := [371285196130096434, 371285196133139589, 371285196093581963, 371285196118329868, 371285196166429138, 371285196169458632, 371285196060458159, 371285195952542306, 371285195843425160, 371285195834689675]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 87020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 87000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362473059118830787, 362473173461642720⟩, ⟨1039638772587132009, 1046358658896117559⟩, true⟩

def words03 : List Nat := [371285195800611174, 371285195813195068, 371285195815459279, 371285195817657814, 371285195643062932, 371285195489626231, 371285195334655010, 371285195312590052, 371285195180158943, 371285195045499523]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 87030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 87000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480076150077966, 362480190519987826⟩, ⟨428861427356964668, 435583672403288302⟩, true⟩

def words04 : List Nat := [371285194909439543, 371285194906534636, 371285194842134355, 371285194820983664, 371285194798957390, 371285194744360974, 371285194530002649, 371285194427826852, 371285194349959862, 371285194353099869]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 87040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 87000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362482090462203397, 362482204859710786⟩, ⟨253530592213706243, 260255239769015653⟩, true⟩

def words05 : List Nat := [371285194297882578, 371285194243817411, 371285194250289288, 371285194269398949, 371285194303034539, 371285194337867074, 371285194352067616, 371285194355107075, 371285194268226086, 371285194237608432]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 87050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 87000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472719534999639, 362472833959473018⟩, ⟨1069406286272421287, 1076133281630076595⟩, true⟩

def words06 : List Nat := [371285194231825971, 371285194234856288, 371285194100120523, 371285193966557881, 371285193831824750, 371285193704300969, 371285193528272688, 371285193473575587, 371285193417883545, 371285193363189914]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 87060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 87000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491053078836093, 362491167530791349⟩, ⟨(-526977605279842885), (-520248216940085101)⟩, true⟩

def words07 : List Nat := [371285193223298564, 371285193216800330, 371285193253428624, 371285193256481966, 371285193210818714, 371285193145855039, 371285193108525006, 371285193111869632, 371285193156410482, 371285193228510254]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 87070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 87000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479019192535611, 362479133671807748⟩, ⟨520964270236513328, 527696037471453360⟩, true⟩

def words08 : List Nat := [371285193299520513, 371285193302551252, 371285193222414598, 371285193250814574, 371285193318054415, 371285193321085218, 371285193212839882, 371285193061025533, 371285192907941167, 371285192875361216]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 87080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 87000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480473585299576, 362480588091831809⟩, ⟨394309232806551819, 401043374262422457⟩, true⟩

def words09 : List Nat := [371285192807849953, 371285192806043537, 371285192803262042, 371285192801321617, 371285192688988448, 371285192618547912, 371285192590531875, 371285192593585747, 371285192542839145, 371285192493373284]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 87090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 87000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 87000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk870
