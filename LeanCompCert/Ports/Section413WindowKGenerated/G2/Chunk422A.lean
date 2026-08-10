import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk422A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk422A
