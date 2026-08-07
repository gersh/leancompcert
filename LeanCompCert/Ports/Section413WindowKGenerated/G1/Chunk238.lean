import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk238

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494924436537081, 362494932134114530⟩, ⟨(-240248076454502781), (-240124203789688875)⟩, true⟩

def state01 : KState := ⟨⟨362492260763612912, 362492268467888121⟩, ⟨(-176633411424792425), (-176509379319009845)⟩, true⟩

def words00 : List Nat := [371284845496263178, 371284846806505357, 371284849274941969, 371284851743470471, 371284853790785652, 371284853791534305, 371284853639083759, 371284853790482171, 371284855221446837, 371284855533558652]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 23800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 23800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502298882924116, 362502306594011730⟩, ⟨(-415614411996463737), (-415490217652160139)⟩, true⟩

def words01 : List Nat := [371284855842836742, 371284856152333605, 371284858225800308, 371284859656615827, 371284861158057396, 371284862659665167, 371284863976711851, 371284863977460832, 371284863678834884, 371284864412002068]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 23810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 23800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478955967544913, 362478963685316711⟩, ⟨140491996056451311, 140616349652563605⟩, true⟩

def words02 : List Nat := [371284865550409286, 371284865551158749, 371284864695030090, 371284863825260025, 371284862955268442, 371284862604154900, 371284862698453719, 371284863627554172, 371284864496528414, 371284864497303810]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 23820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 23800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362547404803737783, 362547412528286783⟩, ⟨(-1490907607226933792), (-1490783092095992178)⟩, true⟩

def words03 : List Nat := [371284865765105078, 371284867280791071, 371284870558293702, 371284872065692550, 371284873041638445, 371284874017718265, 371284875883330360, 371284877055970182, 371284879679612105, 371284882303376084]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 23830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 23800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362521952110935271, 362521959842261994⟩, ⟨(-883946221232063094), (-883821544485714204)⟩, true⟩

def words04 : List Nat := [371284884924172303, 371284886557264974, 371284889773418045, 371284892989679866, 371284896592205157, 371284897852031706, 371284899108677903, 371284900365482650, 371284902334291883, 371284903888864413]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 23840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 23800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362472126384206673, 362472134122281240⟩, ⟨304742054235000244, 304866891951952214⟩, true⟩

def words05 : List Nat := [371284906028471323, 371284908168193875, 371284910305047394, 371284910305797635, 371284910205554819, 371284910310483889, 371284912173329567, 371284912174080006, 371284911978521315, 371284911443821557]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 23850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 23800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362503828458843214, 362503836203649221⟩, ⟨(-451837072820808091), (-451712074458779305)⟩, true⟩

def words06 : List Nat := [371284911836300909, 371284911988847303, 371284912867801525, 371284913746985340, 371284914221645551, 371284914222396248, 371284912358378407, 371284911774639955, 371284912362280858, 371284913155831418]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 23860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 23800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362520171825354693, 362520179576997729⟩, ⟨(-841947543522129184), (-841822381925351580)⟩, true⟩

def words07 : List Nat := [371284913989141303, 371284914822644117, 371284917411762129, 371284919303233940, 371284921714327671, 371284924125498705, 371284926183803377, 371284926184554666, 371284927382514231, 371284928859610461]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 23870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 23800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472470997271408, 362472478755607906⟩, ⟨297328822144130067, 297454143616276743⟩, true⟩

def words08 : List Nat := [371284930793260915, 371284930794012298, 371284930391759597, 371284929915835570, 371284929439659300, 371284929139026274, 371284928564975902, 371284929155675966, 371284929744516926, 371284929745294649]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 23880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 23800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362538469882293790, 362538477647424732⟩, ⟨(-1279783924345906224), (-1279658440519802058)⟩, true⟩

def words09 : List Nat := [371284929412658640, 371284929601541487, 371284931543445568, 371284931824767474, 371284931825355686, 371284931709591774, 371284932722898108, 371284933211559297, 371284935452423073, 371284937693426163]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 23890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 23800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 23800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk238
