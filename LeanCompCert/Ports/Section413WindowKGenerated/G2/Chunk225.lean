import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk225

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360625420995416698, 360625423964701847⟩, ⟨(-1015727912243147465), (-1015682709749241103)⟩, true⟩

def state01 : KState := ⟨⟨360610934163306104, 360610937135332225⟩, ⟨(-689742860626477594), (-689697596446879126)⟩, true⟩

def words00 : List Nat := [360580288493615996, 360580290507900774, 360580291248432907, 360580291988930122, 360580291989178088, 360580292247050505, 360580294462603540, 360580296678016044, 360580297526126095, 360580298887522405]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 22500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 22500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360611498935306723, 360611501910087151⟩, ⟨(-702303746858077160), (-702258420665557156)⟩, true⟩

def words01 : List Nat := [360580302217462907, 360580305547198041, 360580310174729881, 360580312842037838, 360580313862475580, 360580314882846314, 360580315305997900, 360580316758310485, 360580318143326208, 360580319528280591]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 22510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 22500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574493884989722, 360574496862544578⟩, ⟨130873869455979453, 130919258142818577⟩, true⟩

def words02 : List Nat := [360580319918766076, 360580319919057591, 360580318350658130, 360580318080905451, 360580317811100890, 360580316230837533, 360580314708418490, 360580312196743380, 360580309685234862, 360580307748392018]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 22520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 22500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360515119908188111, 360515122888493233⟩, ⟨1469103300077744700, 1469148750741750522⟩, true⟩

def words03 : List Nat := [360580309197510098, 360580310904438682, 360580310904703313, 360580310781405766, 360580309883029256, 360580308482117628, 360580307081242544, 360580306823373515, 360580305405189222, 360580302513637056]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 22530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 22500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360632293157009514, 360632296140067989⟩, ⟨(-1172509245967335602), (-1172463733229213352)⟩, true⟩

def words04 : List Nat := [360580299622270131, 360580299231960325, 360580301732688265, 360580304233250032, 360580305032962853, 360580305033254681, 360580303878617347, 360580302659449161, 360580302182635947, 360580304488556783]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 22540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 22500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360582309593116589, 360582312578952955⟩, ⟨(-45022816069058349), (-44977240675491135)⟩, true⟩

def words05 : List Nat := [360580305802728395, 360580307116815290, 360580309266238029, 360580312937185713, 360580315465147570, 360580317992931677, 360580319381766206, 360580319382058207, 360580318906604553, 360580318995305267]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 22550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 22500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566149299198627, 360566152287788512⟩, ⟨319275692565821875, 319321330092823721⟩, true⟩

def words06 : List Nat := [360580318995547254, 360580318067250676, 360580316151403508, 360580312989151568, 360580309827132443, 360580306164069471, 360580303484024038, 360580302762725537, 360580302041452646, 360580300330770029]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 22560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 22500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360657398079198697, 360657401070545942⟩, ⟨(-1740709056418051821), (-1740663356644184467)⟩, true⟩

def words07 : List Nat := [360580301035210780, 360580302366448713, 360580305655101133, 360580306993737659, 360580306994011993, 360580306449596140, 360580306801110093, 360580308933214256, 360580312347628700, 360580315761806552]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 22570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 22500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360619581683045503, 360619584677180794⟩, ⟨(-886842637071428316), (-886796874329411500)⟩, true⟩

def words08 : List Nat := [360580317916999265, 360580320127513164, 360580322612516013, 360580325097382507, 360580327081934095, 360580328201041949, 360580328333184162, 360580328465346546, 360580328507109123, 360580330245135758]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 22580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 22500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360547705599574737, 360547708596464783⟩, ⟨737297412271779889, 737343237257150467⟩, true⟩

def words09 : List Nat := [360580331654313079, 360580333063420660, 360580333097544217, 360580333939904569, 360580334283307512, 360580334626762620, 360580336209641732, 360580336209934221, 360580335846803765, 360580334403423064]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 22590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 22500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 22500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk225
