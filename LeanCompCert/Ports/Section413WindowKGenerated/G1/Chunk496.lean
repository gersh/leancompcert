import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk496

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362468101796281934, 362468137321546135⟩, ⟨834657485347786070, 835847932154341014⟩, true⟩

def state01 : KState := ⟨⟨362492568752024991, 362492604292124953⟩, ⟨(-378937492368642864), (-377746309633610818)⟩, true⟩

def words00 : List Nat := [371284988790104299, 371284988791958693, 371284988975049328, 371284989270536920, 371284989495276059, 371284989496935220, 371284989491263390, 371284989680022129, 371284989972527691, 371284990127733314]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 49600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 49600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489674563357987, 362489710118495024⟩, ⟨(-235281526001609085), (-234089597199431033)⟩, true⟩

def words01 : List Nat := [371284990249283903, 371284990371370998, 371284990898144826, 371284991222270238, 371284991671836848, 371284992122071102, 371284992518316603, 371284992519971600, 371284992470410669, 371284992567514604]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 49610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 49600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362472736796994278, 362472772366892695⟩, ⟨605210188130495349, 606402849469517455⟩, true⟩

def words02 : List Nat := [371284992771192720, 371284992772848542, 371284992504621248, 371284992128435182, 371284991751618268, 371284991492176511, 371284991030571733, 371284990974781788, 371284990918447449, 371284990840587427]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 49620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 49600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362510550325445342, 362510585910322194⟩, ⟨(-1271637846036443585), (-1270444441244381961)⟩, true⟩

def words03 : List Nat := [371284990690250028, 371284990786988888, 371284991287870858, 371284991498568786, 371284991651420785, 371284991804754436, 371284992119703361, 371284992232159175, 371284992748868649, 371284993266313323]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 49630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 49600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487056066161287, 362487091665980206⟩, ⟨(-105343516400488138), (-104149369808120268)⟩, true⟩

def words04 : List Nat := [371284993784063873, 371284993785719749, 371284993948246701, 371284994135402817, 371284994447783642, 371284994449439742, 371284994267028225, 371284994055035158, 371284993992995624, 371284994037134702]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 49640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 49600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362473315132227492, 362473350746957944⟩, ⟨576999807422654464, 578194694450044160⟩, true⟩

def words05 : List Nat := [371284994163902923, 371284994291303798, 371284994414750885, 371284994416419500, 371284994252198223, 371284994214906334, 371284994278935157, 371284994280620346, 371284994046307676, 371284993813700797]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 49650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 49600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362500525366160510, 362500560995707180⟩, ⟨(-774349777234988072), (-773154154358596074)⟩, true⟩

def words06 : List Nat := [371284993688027239, 371284993689870886, 371284993969441169, 371284994312723940, 371284994495944609, 371284994497605011, 371284994431616934, 371284994602258377, 371284995176509468, 371284995491603003]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 49660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 49600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491318294352609, 362491353939056777⟩, ⟨(-316917951044549855), (-315721575222638851)⟩, true⟩

def words07 : List Nat := [371284995804382655, 371284996117742721, 371284996699256164, 371284997118953060, 371284997655653169, 371284998192960963, 371284998690055688, 371284998703718535, 371284998832786724, 371284998962803831]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 49670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 49600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481207540272927, 362481243199728750⟩, ⟨185483664119992856, 186680772881932876⟩, true⟩

def words08 : List Nat := [371284999496141021, 371284999497798455, 371284999491843894, 371284999487403864, 371284999568455365, 371284999570322520, 371284999733874563, 371284999921229435, 371285000106302001, 371285000108017781]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 49680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 49600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491549263683635, 362491584938135120⟩, ⟨(-328504034323410950), (-327306180352420594)⟩, true⟩

def words09 : List Nat := [371285000120136049, 371285000208693096, 371285000418814091, 371285000420471920, 371285000091588261, 371284999693714267, 371284999299563146, 371284999301419094, 371284999298822831, 371284999433208612]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 49690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 49600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 49600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk496
