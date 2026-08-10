import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk697A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk697B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk697A

def state06 : KState := ⟨⟨362458541750769960, 362458613953344226⟩, ⟨1863311572739553624, 1866713289471592150⟩, true⟩

def words05 : List Nat := [371285375256390908, 371285375171699176, 371285375086182229, 371285375001760993, 371285374643019948, 371285374292942454, 371285373941663453, 371285373775336346, 371285373412337068, 371285373031461652]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 69750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 69700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473040537438829, 362473112761415378⟩, ⟨851888468395844430, 855291678256755246⟩, true⟩

def words06 : List Nat := [371285372649498773, 371285372473606214, 371285372240869588, 371285372214070081, 371285372186548987, 371285372126498190, 371285371792125177, 371285371664026780, 371285371534657494, 371285371492650247]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 69760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 69700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475792478721739, 362475864724417690⟩, ⟨659875226964288952, 663279952298955738⟩, true⟩

def words07 : List Nat := [371285371318744304, 371285371144533490, 371285370969388349, 371285370901729237, 371285370752870309, 371285370668654626, 371285370583573413, 371285370498906806, 371285370159401587, 371285370026113004]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 69770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 69700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470535269490857, 362470607536499300⟩, ⟨1026773344946775716, 1030179557576102550⟩, true⟩

def words08 : List Nat := [371285369926152538, 371285369928547012, 371285369795247408, 371285369619849121, 371285369443493254, 371285369282799956, 371285369018573394, 371285368906615149, 371285368793875221, 371285368670724492]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 69780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 69700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479762493759144, 362479834782362805⟩, ⟨382779477022070635, 386187196891107305⟩, true⟩

def words09 : List Nat := [371285368460840036, 371285368430665041, 371285368543805754, 371285368546194959, 371285368419326863, 371285368230647506, 371285368041059401, 371285367885800587, 371285367626784648, 371285367550226575]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 69790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 69700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 69700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk697B
