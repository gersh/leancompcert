import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk422

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360641547891798193, 360641558909119220⟩, ⟨(-2491339990450552194), (-2491025781614565034)⟩, true⟩

def state01 : KState := ⟨⟨360605832751291627, 360605843774091674⟩, ⟨(-984264375968757960), (-983949935891734728)⟩, true⟩

def words00 : List Nat := [360582532369688395, 360582532920150317, 360582533455377676, 360582533990739870, 360582534220635478, 360582534221210088, 360582534085086011, 360582533519450490, 360582532953731874, 360582533501037453]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 42200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 42200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360547281057873866, 360547292086080889⟩, ⟨1487466325757651357, 1487780994090951271⟩, true⟩

def words01 : List Nat := [360582533930558975, 360582534360166772, 360582534508456781, 360582534509031341, 360582534099289131, 360582533546184846, 360582532992946851, 360582532244979961, 360582531693105745, 360582530859034252]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 42210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 42200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360612392491848875, 360612403525481738⟩, ⟨(-1261785120523499136), (-1261470223085567514)⟩, true⟩

def words02 : List Nat := [360582530024872279, 360582529816282884, 360582530442082298, 360582531067975196, 360582531205190046, 360582531205764959, 360582531346550836, 360582531697416792, 360582532101181098, 360582532809110221]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 42220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 42200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360626427713043277, 360626438752155229⟩, ⟨(-1854655019172328549), (-1854339890324251263)⟩, true⟩

def words03 : List Nat := [360582533082422766, 360582533355776377, 360582534053347173, 360582535029614052, 360582535862422928, 360582536695286141, 360582537139497930, 360582537619604310, 360582538659395170, 360582539699331569]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 42230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 42200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360615459378113605, 360615470422633434⟩, ⟨(-1391392759257126446), (-1391077401953158942)⟩, true⟩

def words04 : List Nat := [360582541116760068, 360582541976888128, 360582542556003529, 360582543135154449, 360582543184133830, 360582543517786406, 360582544276450954, 360582545035189595, 360582545513112838, 360582546292980807]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 42240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 42200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360611512487986626, 360611523537939996⟩, ⟨(-1224733860837317914), (-1224418273939293174)⟩, true⟩

def words05 : List Nat := [360582546922360340, 360582547551885553, 360582548199968410, 360582548542572454, 360582548543108093, 360582548406952449, 360582548693287419, 360582549394702120, 360582550080791506, 360582550766970561]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 42250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 42200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360628332137675479, 360628343193104600⟩, ⟨(-1935761320750736153), (-1935445502420116745)⟩, true⟩

def words06 : List Nat := [360582551172518366, 360582551778644013, 360582552545642613, 360582553312777011, 360582553855498023, 360582554412658484, 360582554660545103, 360582554908482798, 360582555506089192, 360582556589938834]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 42260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 42200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571966962209347, 360571978023066230⟩, ⟨447179178606530698, 447495226395246102⟩, true⟩

def words07 : List Nat := [360582558001324267, 360582559412752866, 360582560279601172, 360582560895002602, 360582561205347890, 360582561515832068, 360582562216020748, 360582562359948559, 360582562360462580, 360582562110729316]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 42270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 42200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601868821130550, 360601879887416106⟩, ⟨(-817067590886863553), (-816751313546790359)⟩, true⟩

def words08 : List Nat := [360582562169172686, 360582562819252675, 360582564027720705, 360582565236245995, 360582565971509828, 360582566150603602, 360582566306448195, 360582566462445789, 360582566779382550, 360582567236650062]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 42280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 42200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360597981536911301, 360597992608682772⟩, ⟨(-652645942972519059), (-652329433607309305)⟩, true⟩

def words09 : List Nat := [360582567317930540, 360582567399265052, 360582568038834154, 360582569127612881, 360582569850664605, 360582570573774378, 360582570936464442, 360582570937040198, 360582571108407008, 360582571473636147]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 42290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 42200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 42200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk422
