import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk609A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk609B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk609A

def state06 : KState := ⟨⟨362499037191869211, 362499091746702890⟩, ⟨(-843013936660440717), (-840767550387071397)⟩, true⟩

def words05 : List Nat := [371285297810074746, 371285297906910703, 371285298272392960, 371285298504710070, 371285298802801155, 371285299101693650, 371285299394979601, 371285299397851247, 371285299625505283, 371285299854339132]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 60950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 60900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362504836350272489, 362504890923529745⟩, ⟨(-1196528247380447237), (-1194280737909864401)⟩, true⟩

def words06 : List Nat := [371285300351437195, 371285300674568418, 371285300947144980, 371285301220364217, 371285301544233060, 371285301735921208, 371285302128997094, 371285302522917939, 371285302915145113, 371285303238599043]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 60960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 60900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507822169033276, 362507876760922626⟩, ⟨(-1378577164120266859), (-1376328518554617827)⟩, true⟩

def words07 : List Nat := [371285303756888178, 371285304276205144, 371285304876142360, 371285305167187336, 371285305416827668, 371285305667114407, 371285306012319785, 371285306224432837, 371285306595968644, 371285306968387991]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 60970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 60900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490144647998580, 362490199258535358⟩, ⟨(-300577940369604070), (-298328157592357016)⟩, true⟩

def words08 : List Nat := [371285307339070109, 371285307351725725, 371285307541002399, 371285307731439057, 371285308001481439, 371285308003548053, 371285307915197978, 371285307809800976, 371285307828765373, 371285307911326879]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 60980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 60900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476889317262862, 362476943946456008⟩, ⟨507945697536855922, 510196618258225234⟩, true⟩

def words09 : List Nat := [371285308103234721, 371285308295981865, 371285308483536047, 371285308485603113, 371285308314673237, 371285308161031758, 371285308092739555, 371285308094842918, 371285307960214850, 371285307825443848]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 60990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 60900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 60900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk609B
