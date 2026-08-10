import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk225A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk225A
