import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk305

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362512181981663106, 362512194889478821⟩, ⟨(-811588284896732800), (-811322176194728774)⟩, true⟩

def state01 : KState := ⟨⟨362489845768596782, 362489858685246313⟩, ⟨(-130392234455057420), (-130125856276502888)⟩, true⟩

def words00 : List Nat := [371285595896906250, 371285595897885560, 371285595460625806, 371285595325183658, 371285595380933309, 371285595381929521, 371285594681538381, 371285593984530450, 371285593660969689, 371285593801883706]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 30500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 30500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362475457958470457, 362475470883961121⟩, ⟨308770871976481590, 309037519943660122⟩, true⟩

def words01 : List Nat := [371285594650588414, 371285595499644101, 371285596126949512, 371285596127937921, 371285596127912939, 371285596164834262, 371285597272523933, 371285597273503739, 371285596952493157, 371285596621836078]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 30510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 30500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482713245992066, 362482726180252708⟩, ⟨87379031164094127, 87645946835191451⟩, true⟩

def words02 : List Nat := [371285596724056757, 371285596725135902, 371285597455715070, 371285598291314319, 371285598732855771, 371285598733835767, 371285597747398483, 371285597139731596, 371285596993087814, 371285596994102535]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 30520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 30500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491509316089754, 362491522259268330⟩, ⟨(-181168460018639838), (-180901272037018612)⟩, true⟩

def words03 : List Nat := [371285596900806347, 371285596810659487, 371285597420885234, 371285597741201635, 371285598353063409, 371285598965274679, 371285599517216206, 371285599518196652, 371285598837240170, 371285599032391771]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 30530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 30500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362448904417873849, 362448917369801950⟩, ⟨1120185002597123765, 1120452457834634383⟩, true⟩

def words04 : List Nat := [371285599674620486, 371285599675601088, 371285598891466567, 371285598110949427, 371285597330095077, 371285596662755662, 371285595466489898, 371285594827352207, 371285594187919016, 371285593391334999]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 30540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 30500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362508652466014670, 362508665426809665⟩, ⟨(-705447727769725308), (-705180001604375084)⟩, true⟩

def words05 : List Nat := [371285592191515993, 371285591890332563, 371285592354716095, 371285592355696937, 371285591697240536, 371285590682513960, 371285589719952143, 371285589721039727, 371285590163861840, 371285590920032912]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 30550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 30500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484355719599217, 362484368689255892⟩, ⟨37203210330647124, 37471207354357382⟩, true⟩

def words06 : List Nat := [371285591578316979, 371285591579315733, 371285592137268881, 371285592770494661, 371285593729671892, 371285593940490506, 371285594075472904, 371285594210784371, 371285594439113874, 371285594440232483]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 30560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 30500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463393894613614, 362463406873104898⟩, ⟨678227679766482256, 678495946908380758⟩, true⟩

def words07 : List Nat := [371285595152102267, 371285595904405895, 371285596636235478, 371285596637217199, 371285595945489536, 371285595574222746, 371285595896662088, 371285595897643855, 371285595169427996, 371285594444946245]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 30570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 30500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476197021262334, 362476210008547108⟩, ⟨286658623372404068, 286927159464932362⟩, true⟩

def words08 : List Nat := [371285593883763625, 371285593884855039, 371285593521807023, 371285593318006980, 371285593113906865, 371285592733916738, 371285591125138718, 371285590451109287, 371285589777351387, 371285589778389048]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 30580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 30500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362467351713103915, 362467364709352606⟩, ⟨557339269999559192, 557608080342193832⟩, true⟩

def words09 : List Nat := [371285589472517919, 371285588925272456, 371285588894951845, 371285588896033854, 371285589039370741, 371285589201133596, 371285589205712259, 371285589206694981, 371285587789923482, 371285587195638299]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 30590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 30500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 30500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk305
