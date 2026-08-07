import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk809

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602301459275687, 360602344125496589⟩, ⟨(-1636000003654319787), (-1633668835086160815)⟩, true⟩

def state01 : KState := ⟨⟨360601651884455354, 360601694561708953⟩, ⟨(-1583572751246916527), (-1581240690080634733)⟩, true⟩

def words00 : List Nat := [360582150851477918, 360582150943360528, 360582151086735430, 360582151230444230, 360582151273261623, 360582151320348677, 360582151321380574, 360582151282429700, 360582151355700496, 360582151598575626]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 80900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 80900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587757290404690, 360587799978583099⟩, ⟨(-459224165928837210), (-456891220781834500)⟩, true⟩

def words01 : List Nat := [360582151993591325, 360582152388824633, 360582152666511297, 360582152872762828, 360582153040709437, 360582153208967583, 360582153529399349, 360582153697682738, 360582153768502101, 360582153839499526]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 80910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 80900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602694797924895, 360602737497029310⟩, ⟨(-1668022286699516485), (-1665688457364355223)⟩, true⟩

def words02 : List Nat := [360582153978231536, 360582154193701505, 360582154561330101, 360582154929171490, 360582155166985606, 360582155309412043, 360582155373352784, 360582155437621206, 360582155654024193, 360582155909536701]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 80920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 80900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360616680263762097, 360616722973901549⟩, ⟨(-2799948811587141239), (-2797614089134157513)⟩, true⟩

def words03 : List Nat := [360582156078246039, 360582156247077227, 360582156568161994, 360582157023184940, 360582157439769572, 360582157856533080, 360582158151399693, 360582158496057639, 360582158924033245, 360582159352385456]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 80930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 80900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360600221779522610, 360600264500580808⟩, ⟨(-1467778600165204375), (-1465442993893952521)⟩, true⟩

def words04 : List Nat := [360582159742699075, 360582159980946078, 360582160142791687, 360582160304759635, 360582160428468795, 360582160629659010, 360582160939515867, 360582161249607629, 360582161435835975, 360582161660666614]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 80940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 80900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360622084224727374, 360622126956720356⟩, ⟨(-3237682572186602999), (-3235346080690481055)⟩, true⟩

def words05 : List Nat := [360582161926214766, 360582162192092021, 360582162610017360, 360582162976929149, 360582163197993498, 360582163419114206, 360582163755422662, 360582164182296405, 360582164676846436, 360582165171654825]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360613532822453962, 360613575565486290⟩, ⟨(-2545331216112931087), (-2542993830815840483)⟩, true⟩

def words06 : List Nat := [360582165590051732, 360582166012551037, 360582166587148540, 360582167162090199, 360582167698669383, 360582168083253327, 360582168385208931, 360582168687284409, 360582168946518118, 360582169335714942]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360576665831548833, 360576708585494892⟩, ⟨439965270050767344, 442303539087997340⟩, true⟩

def words07 : List Nat := [360582169675320214, 360582170015131123, 360582170278480280, 360582170389785438, 360582170420281384, 360582170451104424, 360582170526939654, 360582170536844204, 360582170537876804, 360582170471628358]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600971953533450, 360601014718438480⟩, ⟨(-1528523806461909907), (-1526184649914558245)⟩, true⟩

def words08 : List Nat := [360582170442657495, 360582170597933390, 360582170703805612, 360582170809879876, 360582170810948912, 360582170786533544, 360582170609788336, 360582170557973164, 360582170604976774, 360582170838872670]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580509807245429, 360580552583191665⟩, ⟨128802643377197460, 131142694205383144⟩, true⟩

def words09 : List Nat := [360582170995862773, 360582171152965707, 360582171284586896, 360582171492787731, 360582171633651757, 360582171774701345, 360582171786584796, 360582171787744061, 360582171647449848, 360582171628799139]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk809
