import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk180

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362546601978401591, 362546606276289352⟩, ⟨(-1096742275237745879), (-1096689948159938603)⟩, true⟩

def state01 : KState := ⟨⟨362478551757137210, 362478556059954555⟩, ⟨128627265089397070, 128679680925925692⟩, true⟩

def words00 : List Nat := [371285688356294982, 371285690163673273, 371285691545282266, 371285692926928271, 371285694897276330, 371285695330834477, 371285697366890554, 371285699402947061, 371285700961153920, 371285700961727233]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 18000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 18000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362547500023680959, 362547504331512941⟩, ⟨(-1113590458278169570), (-1113537952103740302)⟩, true⟩

def words01 : List Nat := [371285701237552720, 371285701910274079, 371285705662387999, 371285705662942317, 371285705312781646, 371285704483330922, 371285705277479445, 371285706342166105, 371285709771954098, 371285713201603184]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 18010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 18000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362455278803217231, 362455283116039746⟩, ⟨548614026907535506, 548666623037708766⟩, true⟩

def words02 : List Nat := [371285716623840140, 371285716624394686, 371285717784145064, 371285719620337280, 371285721492844866, 371285721493399462, 371285719269964685, 371285717029117730, 371285714788302331, 371285713877162193]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 18020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 18000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362397630616828241, 362397634934661158⟩, ⟨1588484954655142984, 1588537641147651624⟩, true⟩

def words03 : List Nat := [371285712189850419, 371285711871993470, 371285711553966743, 371285711230490024, 371285707371575584, 371285704439842402, 371285701508149026, 371285700504180216, 371285696225738668, 371285691344924332]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 18030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 18000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362513136765985475, 362513141088784798⟩, ⟨(-495712251380281450), (-495659475268727768)⟩, true⟩

def words04 : List Nat := [371285686464396253, 371285684653416005, 371285681523602513, 371285681462627945, 371285681401493942, 371285680835600374, 371285677741465476, 371285677715415650, 371285680729467708, 371285682251309383]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 18040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 18000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362489351348882284, 362489355676740700⟩, ⟨(-66291678847390707), (-66238811393952233)⟩, true⟩

def words05 : List Nat := [371285683115590399, 371285683979954821, 371285686096387549, 371285686992223904, 371285688198042475, 371285689403943944, 371285690625236031, 371285690625791575, 371285687967776370, 371285688171541988]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 18050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 18000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362465921362295417, 362465925695100009⟩, ⟨357171864834316194, 357224821641781734⟩, true⟩

def words06 : List Nat := [371285691438898768, 371285691970378709, 371285692326620454, 371285692683012737, 371285693960679757, 371285693961291645, 371285694045319489, 371285694377485021, 371285694638719040, 371285694639297120]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 18060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 18000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362544606366652566, 362544610704488118⟩, ⟨(-1065150098611502275), (-1065097050869228345)⟩, true⟩

def words07 : List Nat := [371285694374622024, 371285695204111137, 371285697162920769, 371285697163486543, 371285696602948449, 371285695534924225, 371285696457875116, 371285697209873799, 371285700468741531, 371285703727502928]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 18070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 18000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475442534651954, 362475446877518702⟩, ⟨185377020464087268, 185430159195472022⟩, true⟩

def words08 : List Nat := [371285706129050859, 371285706129607379, 371285704669424806, 371285704880646446, 371285706014448460, 371285706015005129, 371285703078696138, 371285700134429527, 371285697300272182, 371285697300912593]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 18080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 18000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362426069707066459, 362426074054936686⟩, ⟨1078997877584932597, 1079051106854618787⟩, true⟩

def words09 : List Nat := [371285698732549597, 371285700730789775, 371285702337572985, 371285702338129902, 371285700454737820, 371285698189059761, 371285696709295796, 371285696709852797, 371285693431456115, 371285690138188323]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 18090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 18000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 18000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk180
