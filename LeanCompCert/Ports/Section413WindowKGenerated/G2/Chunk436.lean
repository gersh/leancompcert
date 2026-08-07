import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk436

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360557048648665799, 360557060440694334⟩, ⟨1138452580987340835, 1138800027916905315⟩, true⟩

def state01 : KState := ⟨⟨360605846617969340, 360605858415625475⟩, ⟨(-989477522079374521), (-989129829759964679)⟩, true⟩

def words00 : List Nat := [360583179108819053, 360583178957809107, 360583179045451447, 360583179133199363, 360583179133756373, 360583178736642137, 360583177815291757, 360583177419670374, 360583177153137563, 360583177673845650]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 43600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 43600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587301341409892, 360587313144730927⟩, ⟨(-180586025238581923), (-180238085844766631)⟩, true⟩

def words01 : List Nat := [360583177929552934, 360583178185313506, 360583178966345458, 360583180009988203, 360583180586620038, 360583181163317443, 360583181301389519, 360583181301985036, 360583181138416094, 360583181233820018]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 43610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 43600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360610158140772424, 360610169949701718⟩, ⟨(-1177740065191046605), (-1177391881136885517)⟩, true⟩

def words02 : List Nat := [360583181747590175, 360583182091413515, 360583182091949287, 360583182081402635, 360583182070748232, 360583182128802743, 360583182879461017, 360583183630201662, 360583184116375322, 360583184735493085]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 43620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 43600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360609228616997951, 360609240431555081⟩, ⟨(-1137270615661888282), (-1136922186036722882)⟩, true⟩

def words03 : List Nat := [360583185170290104, 360583185605239331, 360583186564873867, 360583187001162228, 360583187001711443, 360583186995498168, 360583187061894394, 360583187537721045, 360583188135199820, 360583188732784734]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 43630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 43600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577317337122860, 360577329157356271⟩, ⟨255231352479614523, 255580029845507325⟩, true⟩

def words04 : List Nat := [360583188990069083, 360583188990664839, 360583188724578039, 360583188685956989, 360583188647189439, 360583188147614526, 360583187270099114, 360583186128521812, 360583184986878397, 360583184369952961]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 43640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 43600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360567951572721978, 360567963398575942⟩, ⟨664266209684633177, 664615132414745361⟩, true⟩

def words05 : List Nat := [360583184626604260, 360583185017498920, 360583185144237487, 360583185388363463, 360583185497997819, 360583185607786565, 360583186123469697, 360583186263998315, 360583186264547784, 360583185916496573]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 43650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 43600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360643803720060250, 360643815551539169⟩, ⟨(-2647834870174379959), (-2647485701830470847)⟩, true⟩

def words06 : List Nat := [360583185743848646, 360583186243942457, 360583187092504288, 360583187941141199, 360583188291443946, 360583188658342360, 360583189175953962, 360583189693720244, 360583190735213144, 360583192124051123]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 43660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 43600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606630593357155, 360606642430519534⟩, ⟨(-1024305663285771491), (-1023956246717164301)⟩, true⟩

def words07 : List Nat := [360583193249051192, 360583194374065051, 360583195267588727, 360583196495325817, 360583197590120841, 360583198684962523, 360583199439160913, 360583199670883588, 360583200208059366, 360583200745422647]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 43670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 43600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573081024091662, 360573092866865021⟩, ⟨441166043181627005, 441515704866435315⟩, true⟩

def words08 : List Nat := [360583201172179709, 360583201172776074, 360583201077105427, 360583200718091010, 360583200358995724, 360583199866043683, 360583199645117236, 360583199355689770, 360583199066210227, 360583198513577460]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 43680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 43600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360625294563330615, 360625306411732886⟩, ⟨(-1840328465785913670), (-1839978558145977088)⟩, true⟩

def words09 : List Nat := [360583198574824112, 360583198867534577, 360583199311066395, 360583199771077578, 360583199782368890, 360583199793701171, 360583200102437879, 360583200674614600, 360583201638614999, 360583202602709158]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 43690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 43600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 43600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk436
