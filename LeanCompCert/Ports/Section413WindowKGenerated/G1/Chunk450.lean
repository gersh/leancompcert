import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk450

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362498967557737885, 362498996568821836⟩, ⟨(-605503308659856654), (-604621245796519142)⟩, true⟩

def state01 : KState := ⟨⟨362487695935251926, 362487724959613074⟩, ⟨(-98265896120879269), (-97383235713627511)⟩, true⟩

def words00 : List Nat := [371285561394365086, 371285561395854256, 371285561292675651, 371285561091938932, 371285560890655178, 371285560839725692, 371285560854274804, 371285561109385901, 371285561366938014, 371285561416574403]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 45000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 45000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500944971449393, 362500974009252268⟩, ⟨(-694656967775343402), (-693773702288056122)⟩, true⟩

def words01 : List Nat := [371285561682052037, 371285561948281892, 371285562707054311, 371285562878477996, 371285562972279727, 371285563066557981, 371285563298317164, 371285563319927616, 371285563663251125, 371285564007202379]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 45010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 45000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476579917657273, 362476608968898004⟩, ⟨402283449286699185, 403167319814285085⟩, true⟩

def words02 : List Nat := [371285564323990704, 371285564325480599, 371285563984759150, 371285563899893612, 371285563878114214, 371285563879604657, 371285563383439605, 371285562886796786, 371285562389584848, 371285562273801719]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 45020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 45000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472723899844036, 362472752964541030⟩, ⟨575976307686733191, 576860784218407035⟩, true⟩

def words03 : List Nat := [371285562076005635, 371285562075869539, 371285562075213347, 371285562014713376, 371285561625533801, 371285561386565323, 371285561272407491, 371285561273923886, 371285560991094343, 371285560708417993]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 45030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 45000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362492722939929904, 362492752017958258⟩, ⟨(-324826912763057194), (-323941835718998670)⟩, true⟩

def words04 : List Nat := [371285560579914506, 371285560581556703, 371285560808787028, 371285561127418668, 371285561310813807, 371285561312304735, 371285560906396007, 371285560922505358, 371285561298634773, 371285561459797086]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 45040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 45000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362492121176254703, 362492150267870778⟩, ⟨(-297632063469841451), (-296746374229422783)⟩, true⟩

def words05 : List Nat := [371285561620184982, 371285561781082617, 371285562433714436, 371285562841705464, 371285563398510587, 371285563955893303, 371285564479762281, 371285564535762641, 371285564682947397, 371285564830924652]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 45050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 45000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476352823851170, 362476381928740407⟩, ⟨413034753310140400, 413921040708306016⟩, true⟩

def words06 : List Nat := [371285565470316133, 371285565471807431, 371285565455134573, 371285565442461801, 371285565564342111, 371285565566015949, 371285565667908916, 371285565775849823, 371285565886386675, 371285565887930740]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 45060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 45000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501988921992457, 362502018040406478⟩, ⟨(-742562353659480267), (-741675456633458453)⟩, true⟩

def words07 : List Nat := [371285565803177879, 371285565922989793, 371285566190991617, 371285566192484693, 371285565910165278, 371285565540910278, 371285565292197133, 371285565293851937, 371285565610632311, 371285565977305983]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 45070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 45000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472293131209419, 362472322263093511⟩, ⟨596244892637525316, 597132396962846448⟩, true⟩

def words08 : List Nat := [371285566342287642, 371285566343779833, 371285566253117245, 371285566454954088, 371285566765190407, 371285566766682685, 371285566421505660, 371285565991529020, 371285565560951482, 371285565385669756]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 45080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 45000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362461801973749033, 362461831119046900⟩, ⟨1069460606876224007, 1070348716098615925⟩, true⟩

def words09 : List Nat := [371285565221865890, 371285565352346466, 371285565481951577, 371285565483469920, 371285565204577080, 371285565014575232, 371285564953692119, 371285564955184746, 371285564431105281, 371285563906543544]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 45090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 45000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 45000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk450
