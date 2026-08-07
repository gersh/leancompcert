import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk510

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478377105126419, 362478414748492824⟩, ⟨335892082001441433, 337189076952466119⟩, true⟩

def state01 : KState := ⟨⟨362469410985601464, 362469448644157579⟩, ⟨793307990239340570, 794605759945816724⟩, true⟩

def words00 : List Nat := [371285026424802165, 371285026426536204, 371285026362906040, 371285026301248261, 371285026261445197, 371285026263323254, 371285026122353641, 371285026151628329, 371285026152925795, 371285026094852459]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 51000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 51000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501892212598741, 362501929886554095⟩, ⟨(-863722806824620765), (-862424251524683975)⟩, true⟩

def words01 : List Nat := [371285025790636288, 371285025776214463, 371285026091929130, 371285026093636376, 371285026013542806, 371285025897952375, 371285025907810208, 371285025909701411, 371285026234096380, 371285026567302715]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 51010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 51000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362470468010907421, 362470505700282987⟩, ⟨739638690921538381, 740938033038768641⟩, true⟩

def words02 : List Nat := [371285026898077642, 371285026899782981, 371285026763393327, 371285026737310042, 371285026746761291, 371285026748467931, 371285026352481693, 371285025954813469, 371285025556491693, 371285025356035266]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 51020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 51000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362465626471091504, 362465664175836433⟩, ⟨986835837425138692, 988135963918302226⟩, true⟩

def words03 : List Nat := [371285025171581560, 371285025272357640, 371285025373006978, 371285025374721013, 371285025196705698, 371285025081649378, 371285024965755716, 371285024950483018, 371285024583841150, 371285024206477466]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 51030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 51000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487657794025873, 362487695514021128⟩, ⟨(-137693380535215523), (-136392475586219099)⟩, true⟩

def words04 : List Nat := [371285023828332312, 371285023769403566, 371285023714614428, 371285023880129400, 371285023970172619, 371285023971878721, 371285023550686640, 371285023513610799, 371285023769342552, 371285023823445308]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 51040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 51000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362495926132089847, 362495963867635342⟩, ⟨(-559867625906173269), (-558565927040053213)⟩, true⟩

def words05 : List Nat := [371285023824762238, 371285023754075959, 371285023891085036, 371285023937497969, 371285024101379071, 371285024265928051, 371285024413932678, 371285024415669331, 371285024462344681, 371285024678684087]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 51050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 51000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491605627507607, 362491643378244622⟩, ⟨(-339166993166549187), (-337864518541533385)⟩, true⟩

def words06 : List Nat := [371285025277038177, 371285025544770400, 371285025812650339, 371285026081118713, 371285026364260529, 371285026457323372, 371285026871585343, 371285027286513712, 371285027662388518, 371285027793694848]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 51060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 51000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502272180888688, 362502309947093953⟩, ⟨(-883918880402554173), (-882615615738193825)⟩, true⟩

def words07 : List Nat := [371285028307219213, 371285028821671968, 371285029532003560, 371285029732334027, 371285029849801740, 371285029967765961, 371285030340100703, 371285030521602747, 371285030861063327, 371285031201264033]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 51070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 51000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490735523257019, 362490773304875842⟩, ⟨(-294654282323215658), (-293350230257691180)⟩, true⟩

def words08 : List Nat := [371285031541413183, 371285031543120414, 371285031472158106, 371285031573559445, 371285031699465913, 371285031701203796, 371285031562136253, 371285031424350952, 371285031470265995, 371285031584606956]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 51080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 51000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472167072571269, 362472204869560076⟩, ⟨654159352696012202, 655464190093193284⟩, true⟩

def words09 : List Nat := [371285031978962834, 371285032373979213, 371285032690675221, 371285032692383444, 371285032550850366, 371285032421700141, 371285032455301076, 371285032457010596, 371285032206515769, 371285031957428828]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 51090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 51000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 51000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk510
