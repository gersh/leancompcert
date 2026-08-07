import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk456

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494506016843216, 362494535838618313⟩, ⟨(-411088441463217285), (-410169653580104481)⟩, true⟩

def state01 : KState := ⟨⟨362480175647482395, 362480205482698999⟩, ⟨242481925543283413, 243401326430904027⟩, true⟩

def words00 : List Nat := [371285541683093172, 371285541684603975, 371285541668440083, 371285541640918121, 371285541612844460, 371285541607738774, 371285541651496132, 371285541869536733, 371285542059219368, 371285542060783431]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 45600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 45600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481890420928668, 362481920269811236⟩, ⟨164332869982622439, 165252894245368079⟩, true⟩

def words01 : List Nat := [371285542128937328, 371285542314895274, 371285542980346155, 371285543005930578, 371285543007100505, 371285542958036054, 371285542935531521, 371285542937196427, 371285542725750159, 371285542648027926]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 45610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 45600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362468926607254128, 362468956469785950⟩, ⟨755711926690247359, 756632573700026865⟩, true⟩

def words02 : List Nat := [371285542569767904, 371285542438654545, 371285541666955047, 371285541292615634, 371285540917535379, 371285540679052112, 371285540041563174, 371285539345139753, 371285538648131281, 371285538380233025]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 45620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 45600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362453984124593746, 362454014000765085⟩, ⟨1437705786423975418, 1438627055873293644⟩, true⟩

def words03 : List Nat := [371285538134430486, 371285538252653014, 371285538253803976, 371285538243728576, 371285537593445885, 371285537089218710, 371285536584248647, 371285536479954136, 371285535878466516, 371285535189544080]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 45630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 45600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362471034446987517, 362471064336690753⟩, ⟨659491699335905925, 660413586450105563⟩, true⟩

def words04 : List Nat := [371285534499937226, 371285534290696848, 371285533841341861, 371285533706639430, 371285533571490038, 371285533310923348, 371285532531992758, 371285531953572865, 371285531374359239, 371285531227960197]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 45640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 45600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362480111878505781, 362480141781956431⟩, ⟨245081281156217077, 246003795911305109⟩, true⟩

def words05 : List Nat := [371285530912189318, 371285530596416359, 371285530378568879, 371285530380263873, 371285530306392651, 371285530288032241, 371285530269156125, 371285530225342488, 371285529629066431, 371285529512922514]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 45650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 45600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362466663393179490, 362466693310125796⟩, ⟨859187898587055617, 860111029623478099⟩, true⟩

def words06 : List Nat := [371285529395980102, 371285529321132638, 371285528791487168, 371285528273039722, 371285527754015764, 371285527380767145, 371285526797321510, 371285526693675819, 371285526589515397, 371285526483535551]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 45660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 45600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502960558447528, 362502990489079341⟩, ⟨(-798659421040061177), (-797735664917956141)⟩, true⟩

def words07 : List Nat := [371285526090142456, 371285526109922546, 371285526607939634, 371285526609453320, 371285526551164918, 371285526360405361, 371285526455672397, 371285526538675152, 371285526922015781, 371285527306029103]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 45670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 45600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480777205785405, 362480807150079590⟩, ⟨214803489182687556, 215727869472337492⟩, true⟩

def words08 : List Nat := [371285527688858661, 371285527793713084, 371285528145352096, 371285528497754141, 371285528994436710, 371285528995950629, 371285528929626809, 371285528807527946, 371285528703824649, 371285528705550642]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 45680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 45600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485125294178888, 362485155252101913⟩, ⟨16223211540518405, 17148214598999065⟩, true⟩

def words09 : List Nat := [371285528978578154, 371285529355526831, 371285529731988800, 371285529783627453, 371285529862006637, 371285529941180281, 371285530498045404, 371285530499559736, 371285530493080074, 371285530486557034]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 45690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 45600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 45600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk456
