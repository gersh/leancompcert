import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk619

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474481859532052, 362474538177821121⟩, ⟨669106043127075922, 671460760938300708⟩, true⟩

def state01 : KState := ⟨⟨362489299809208757, 362489356146329818⟩, ⟨(-248207182607097002), (-245851299001631684)⟩, true⟩

def words00 : List Nat := [371285385512285864, 371285385402252805, 371285385210843636, 371285385229746090, 371285385231370984, 371285385210406518, 371285384939759167, 371285384886067186, 371285385036111049, 371285385102428062]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 61900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 61900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480447680049925, 362480504036337484⟩, ⟨299930741079261342, 302287811375695548⟩, true⟩

def words01 : List Nat := [371285385166329084, 371285385230940024, 371285385516036698, 371285385696024848, 371285385855548234, 371285386015827695, 371285386174415793, 371285386176516615, 371285386021620909, 371285385945435929]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 61910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 61900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482047043329251, 362482103418331073⟩, ⟨200916681273883358, 203274910456890810⟩, true⟩

def words02 : List Nat := [371285385978674466, 371285385980811825, 371285385876645245, 371285385772197817, 371285385666970010, 371285385642681317, 371285385592039525, 371285385698770436, 371285385749590068, 371285385751779433]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 61920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 61900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362505735435038353, 362505791829014030⟩, ⟨(-1266226112200555251), (-1263866707873498085)⟩, true⟩

def words03 : List Nat := [371285385812092930, 371285385926476307, 371285386300657909, 371285386360708013, 371285386380694512, 371285386401403189, 371285386656270835, 371285386802430272, 371285387133289849, 371285387465056821]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 61930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 61900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484928231779291, 362484984644729541⟩, ⟨22583715191297321, 24944294899049205⟩, true⟩

def words04 : List Nat := [371285387747621442, 371285387749722939, 371285387726033561, 371285387769844375, 371285387860768646, 371285387862870939, 371285387654937311, 371285387448852044, 371285387294344183, 371285387296786023]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 61940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 61900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362469680193144480, 362469736625029209⟩, ⟨967339973540633942, 969701726336312200⟩, true⟩

def words05 : List Nat := [371285387482771405, 371285387676150351, 371285387869068416, 371285387871170209, 371285387716726979, 371285387641908383, 371285387566773058, 371285387568884986, 371285387322730280, 371285387072516884]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 61950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 61900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478467088409391, 362478523539100413⟩, ⟨422901877402921329, 425264795533818031⟩, true⟩

def words06 : List Nat := [371285386829443445, 371285386831762911, 371285386732169551, 371285386727857239, 371285386722891687, 371285386650528502, 371285386230351401, 371285386071924623, 371285385967060404, 371285385969236509]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 61960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 61900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489897070726814, 362489953540570732⟩, ⟨(-285501852614912257), (-283137747480515011)⟩, true⟩

def words07 : List Nat := [371285385860106972, 371285385697701886, 371285385563312202, 371285385565666234, 371285385506213318, 371285385481115828, 371285385455290421, 371285385438190868, 371285385326511269, 371285385402794954]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 61970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 61900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482103628332451, 362482160116891317⟩, ⟨197611952882984139, 199977218067951013⟩, true⟩

def words08 : List Nat := [371285385738425574, 371285385808410980, 371285385846618743, 371285385885560879, 371285385887076102, 371285385872869629, 371285385842552732, 371285385959177928, 371285386074031598, 371285386076208432]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 61980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 61900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491544431887017, 362491600939520577⟩, ⟨(-387601486378442446), (-385235038661746784)⟩, true⟩

def words09 : List Nat := [371285386234002150, 371285386445008117, 371285386873580666, 371285386982279347, 371285387051133006, 371285387120635582, 371285387308188304, 371285387367084874, 371285387468759451, 371285387571370681]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 61990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 61900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 61900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk619
