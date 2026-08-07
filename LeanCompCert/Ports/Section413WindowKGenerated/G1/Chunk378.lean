import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk378

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496572247983938, 362496592430200358⟩, ⟨(-442494347133116543), (-441978796178352275)⟩, true⟩

def state01 : KState := ⟨⟨362474414031340441, 362474434224538749⟩, ⟨395266514123999901, 395782480251871563⟩, true⟩

def words00 : List Nat := [371284901092386211, 371284901202699225, 371284901311690258, 371284901421086943, 371284901741346049, 371284901742705320, 371284901771673900, 371284901830821623, 371284901890020195, 371284901891300238]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 37800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 37800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362535414150290545, 362535434354629626⟩, ⟨(-1911405874284935417), (-1910889486868615013)⟩, true⟩

def words01 : List Nat := [371284902038167113, 371284902462480593, 371284903585805835, 371284904242825800, 371284904787660996, 371284905332863693, 371284906343309338, 371284907117775154, 371284908454605608, 371284909791903400]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 37810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 37800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488257603349912, 362488277818845739⟩, ⟨(-127764054534537268), (-127247245113753270)⟩, true⟩

def words02 : List Nat := [371284910995805836, 371284911268520997, 371284912157898208, 371284913047885193, 371284913960627398, 371284913961862277, 371284913943420056, 371284913936668209, 371284914157766509, 371284914248093876]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 37820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 37800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362465417964820136, 362465438191436373⟩, ⟨736502970605767786, 737020200768536302⟩, true⟩

def words03 : List Nat := [371284915036789162, 371284915825955502, 371284916613348576, 371284916614583857, 371284916471064233, 371284916274515471, 371284916494295881, 371284916495531310, 371284915982796669, 371284915469469369]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 37830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 37800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476438115936640, 362476458353619106⟩, ⟨319557334131195938, 320074983095962114⟩, true⟩

def words04 : List Nat := [371284915066896202, 371284915068284697, 371284915176915070, 371284915373752963, 371284915446675103, 371284915447911066, 371284914680404628, 371284914611856642, 371284914758761135, 371284914760041721]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 37840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 37800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362478067917331480, 362478088166265524⟩, ⟨257901139847315209, 258419214741538011⟩, true⟩

def words05 : List Nat := [371284914537560167, 371284914163660574, 371284914112123993, 371284914113499359, 371284914260010117, 371284914423658252, 371284914585802278, 371284914587040239, 371284913997833952, 371284913819058486]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 37850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 37800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477515841019067, 362477536100970244⟩, ⟨278862030426515298, 279380522488307376⟩, true⟩

def words06 : List Nat := [371284914157134928, 371284914158379581, 371284914056485016, 371284913804821260, 371284913552687089, 371284913512015817, 371284913238063932, 371284913354690943, 371284913457008938, 371284913458310839]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 37860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 37800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362508604052443104, 362508624323574226⟩, ⟨(-898591999187194663), (-898073083684491535)⟩, true⟩

def words07 : List Nat := [371284913766998930, 371284914271132632, 371284915125181946, 371284915227882121, 371284915228840299, 371284915189795365, 371284915394630551, 371284915395993273, 371284915951432829, 371284916578697257]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 37870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 37800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362509667520286953, 362509687802598123⟩, ⟨(-938952040439051958), (-938432701381087478)⟩, true⟩

def words08 : List Nat := [371284917128457951, 371284917190027406, 371284917819042835, 371284918448687141, 371284919288664023, 371284919415300158, 371284919547475079, 371284919680078791, 371284920508976522, 371284921164045932]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 37880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 37800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486221593003249, 362486241886448150⟩, ⟨(-50454542217629555), (-49934781243973293)⟩, true⟩

def words09 : List Nat := [371284922104037560, 371284923044456799, 371284923904494850, 371284923905732446, 371284923837797844, 371284923751869367, 371284924274392788, 371284924308967802, 371284924344666220, 371284924380808617]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 37890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 37800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 37800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk378
