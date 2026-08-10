import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk609A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496364195575228, 362496418638829094⟩, ⟨(-680147133140567356), (-677907545443726512)⟩, true⟩

def state01 : KState := ⟨⟨362477806872407685, 362477861334006308⟩, ⟨450147139891949089, 452387844881918861⟩, true⟩

def words00 : List Nat := [371285287788879139, 371285287931205483, 371285288038985609, 371285288147465534, 371285288303856792, 371285288326768553, 371285288379665875, 371285288433347596, 371285288484142210, 371285288486278217]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 60900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 60900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362520994178848622, 362521048659136430⟩, ⟨(-2180632063944390170), (-2178390220505787504)⟩, true⟩

def words01 : List Nat := [371285288413193809, 371285288463162095, 371285288781813131, 371285288928895583, 371285289041798633, 371285289155320807, 371285289537789457, 371285289857314453, 371285290445694361, 371285291034991952]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 60910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 60900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362500148027069838, 362500202526019989⟩, ⟨(-910600181665779287), (-908357201222793281)⟩, true⟩

def words02 : List Nat := [371285291565935463, 371285291774203572, 371285292251545874, 371285292729919615, 371285293290368191, 371285293540309018, 371285293770166219, 371285294000785828, 371285294314202729, 371285294561252912]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 60920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 60900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480037553723166, 362480092071219227⟩, ⟨314884793878075878, 317128904420599670⟩, true⟩

def words03 : List Nat := [371285294951934934, 371285295343417890, 371285295729144534, 371285295756284687, 371285295798237084, 371285295841201568, 371285296152741575, 371285296154806406, 371285296107441264, 371285296024360360]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 60930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 60900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494109761711794, 362494164297713822⟩, ⟨(-542672385652957927), (-540427147262798331)⟩, true⟩

def words04 : List Nat := [371285296088764567, 371285296140425906, 371285296460773509, 371285296781988333, 371285297025967491, 371285297028034310, 371285297130689200, 371285297293780071, 371285297566328599, 371285297713945504]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 60940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 60900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk609A
