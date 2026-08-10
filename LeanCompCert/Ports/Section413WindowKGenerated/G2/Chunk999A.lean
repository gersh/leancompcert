import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk999A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579737106737746, 360579803240178417⟩, ⟨258883091682179594, 263344103389695322⟩, true⟩

def state01 : KState := ⟨⟨360592818948375575, 360592885095497017⟩, ⟨(-1048042780745639856), (-1043580402259437918)⟩, true⟩

def words00 : List Nat := [360582439365854911, 360582439468096718, 360582439519949836, 360582439571986111, 360582439573209245, 360582439576501281, 360582439703695348, 360582439831165587, 360582439889285540, 360582439995335279]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595339210211251, 360595405371069922⟩, ⟨(-1299938547630846175), (-1295474796592038889)⟩, true⟩

def words01 : List Nat := [360582440097787104, 360582440200645310, 360582440292678390, 360582440294131698, 360582440286376020, 360582440193667752, 360582440100683159, 360582440118572343, 360582440249503349, 360582440380761659]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595653177852715, 360595719352540975⟩, ⟨(-1331406997168639903), (-1326941864207571601)⟩, true⟩

def words02 : List Nat := [360582440451864333, 360582440455190578, 360582440558359369, 360582440661964023, 360582440694396186, 360582440695853618, 360582440694194698, 360582440642382594, 360582440637141109, 360582440771678104]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567740903748963, 360567807092145492⟩, ⟨1458047884962449154, 1462514387859353524⟩, true⟩

def words03 : List Nat := [360582440935608108, 360582441099834089, 360582441213686334, 360582441273321243, 360582441274547701, 360582441246303089, 360582441227940740, 360582441229394489, 360582441161298984, 360582441016378626]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360600584371114686, 360600650573230123⟩, ⟨(-1824506416292216515), (-1820038542258934625)⟩, true⟩

def words04 : List Nat := [360582440871127971, 360582440808078785, 360582440814359466, 360582440835564018, 360582440836917184, 360582440772604900, 360582440847740417, 360582440925018695, 360582441081555653, 360582441265246622]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk999A
