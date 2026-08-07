import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk961

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483764336196085, 362483904792185801⟩, ⟨122015273735125127, 131128450224249791⟩, true⟩

def state01 : KState := ⟨⟨362485138879662897, 362485279365839803⟩, ⟨(-10069206591501715), (-953128957145415)⟩, true⟩

def words00 : List Nat := [371285269334081865, 371285269351974624, 371285269413286113, 371285269475960664, 371285269515695941, 371285269519069092, 371285269441520118, 371285269420875801, 371285269445226300, 371285269448879652]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 96100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 96100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491996545033968, 362492137061956791⟩, ⟨(-669199415304849095), (-660080382529768637)⟩, true⟩

def words01 : List Nat := [371285269451422530, 371285269447441928, 371285269529648449, 371285269571729794, 371285269638316745, 371285269706163107, 371285269754209119, 371285269757612147, 371285269804453841, 371285269880149176]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 96110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 96100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487739681363992, 362487880228304266⟩, ⟨(-259981438439131941), (-250859520228278427)⟩, true⟩

def words02 : List Nat := [371285270033490817, 371285270084530237, 371285270133869938, 371285270184380774, 371285270265682088, 371285270297635224, 371285270418179580, 371285270540142965, 371285270638626412, 371285270669262664]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 96120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 96100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362503379801011381, 362503520378440708⟩, ⟨(-1763573378039493406), (-1754448528766510780)⟩, true⟩

def words03 : List Nat := [371285270737953498, 371285270808313859, 371285270975878307, 371285271014315258, 371285271037684815, 371285271062113310, 371285271193461242, 371285271290001417, 371285271482105238, 371285271675714853]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 96130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 96100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493184132639285, 362493324740443076⟩, ⟨(-783346088381600832), (-774218318751269202)⟩, true⟩

def words04 : List Nat := [371285271870562375, 371285271937758528, 371285272100878682, 371285272265790805, 371285272414539555, 371285272420001635, 371285272424951918, 371285272431003787, 371285272543988562, 371285272631585641]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 96140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 96100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362483122834929171, 362483263473162298⟩, ⟨184133158605844267, 193263854171051257⟩, true⟩

def words05 : List Nat := [371285272772835013, 371285272915544312, 371285273056586557, 371285273065689627, 371285273106312948, 371285273148605389, 371285273297421020, 371285273303110408, 371285273305680162, 371285273288617488]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 96150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 96100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362493288398122587, 362493429066528697⟩, ⟨(-793420696343340183), (-784287099188222737)⟩, true⟩

def words06 : List Nat := [371285273317267173, 371285273342323001, 371285273421879887, 371285273502776822, 371285273564743821, 371285273568175512, 371285273617588125, 371285273699344749, 371285273847280689, 371285273935572503]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 96160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 96100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493396896604577, 362493537595755638⟩, ⟨(-803869335412535657), (-794732781360211843)⟩, true⟩

def words07 : List Nat := [371285274022481821, 371285274110498864, 371285274209868004, 371285274270517282, 371285274362946321, 371285274456707947, 371285274548880167, 371285274552260612, 371285274618144345, 371285274708268919]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 96170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 96100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485249654532735, 362485390383692054⟩, ⟨(-20197402610240752), (-11057962207278802)⟩, true⟩

def words08 : List Nat := [371285274904690200, 371285274958054177, 371285275010918102, 371285275064952727, 371285275150146787, 371285275201621715, 371285275274266190, 371285275348201001, 371285275420617058, 371285275425305020]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 96180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 96100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499529965990873, 362499670725695534⟩, ⟨(-1393895359651018946), (-1384752980944218832)⟩, true⟩

def words09 : List Nat := [371285275517332071, 371285275611195976, 371285275765940555, 371285275831978438, 371285275868285242, 371285275905593665, 371285276003133585, 371285276048296929, 371285276200217197, 371285276353693744]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 96190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 96100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 96100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk961
