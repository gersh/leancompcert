import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk487

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362462802562062093, 362462836759140098⟩, ⟨1081208982128709976, 1082334146487302962⟩, true⟩

def state01 : KState := ⟨⟨362489964563474592, 362489998775073865⟩, ⟨(-241664083001036488), (-240538211383666746)⟩, true⟩

def words00 : List Nat := [371285060824357299, 371285060722638589, 371285060483188239, 371285060559481999, 371285060560741063, 371285060543282376, 371285060215750045, 371285060232321609, 371285060604406955, 371285060707463189]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 48700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 48700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362475030761859525, 362475064988277101⟩, ⟨485899455383865246, 487026048873423262⟩, true⟩

def words01 : List Nat := [371285060803409138, 371285060899906578, 371285061172591404, 371285061270947149, 371285061499442726, 371285061728538370, 371285061954377930, 371285061956000686, 371285061620969017, 371285061417851679]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 48710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 48700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362465883456549595, 362465917697411429⟩, ⟨931648090698994557, 932775387989440197⟩, true⟩

def words02 : List Nat := [371285061379831609, 371285061381458882, 371285061116457966, 371285060832574619, 371285060548090285, 371285060388149977, 371285060019014561, 371285059827424097, 371285059635280879, 371285059404532083]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 48720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 48700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362494706800611356, 362494741056119598⟩, ⟨(-472969784230760225), (-471841773145573901)⟩, true⟩

def words03 : List Nat := [371285059039766975, 371285059068627844, 371285059516370919, 371285059639288201, 371285059718544121, 371285059798308511, 371285060035994953, 371285060063174940, 371285060262905474, 371285060463330251]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 48730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 48700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362465209273032425, 362465243543205808⟩, ⟨964816476950799914, 965945202889974722⟩, true⟩

def words04 : List Nat := [371285060523065851, 371285060524689483, 371285060024044313, 371285059900595841, 371285059781570650, 371285059783194367, 371285059229535788, 371285058678207290, 371285058126227863, 371285057803777911]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 48740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 48700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362459320866132467, 362459355150927936⟩, ⟨1252006058159734737, 1253135496999937335⟩, true⟩

def words05 : List Nat := [371285057411396783, 371285057426145703, 371285057437690808, 371285057439318134, 371285057016421734, 371285056630046259, 371285056273886866, 371285056275510862, 371285055747888799, 371285055222646557]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 48750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 48700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362466831093462386, 362466865392816530⟩, ⟨885854372116392024, 886984520910246180⟩, true⟩

def words06 : List Nat := [371285054696686688, 371285054590711068, 371285054339084698, 371285054198874668, 371285054058179922, 371285053845446029, 371285053146551633, 371285052867711510, 371285052588037739, 371285052485720165]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 48760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 48700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469693163691985, 362469727477842594⟩, ⟨746252704803656848, 747383575295067360⟩, true⟩

def words07 : List Nat := [371285052114038029, 371285051740409518, 371285051366156443, 371285051148799620, 371285050786291770, 371285050548504737, 371285050310126106, 371285050038455781, 371285049306440666, 371285048994351308]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 48770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 48700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362464112230570105, 362464146559210049⟩, ⟨1018507759002042117, 1019639336358352935⟩, true⟩

def words08 : List Nat := [371285048786260951, 371285048787885573, 371285048334648593, 371285047777705476, 371285047220150669, 371285046677570660, 371285045966710350, 371285045675391127, 371285045383569076, 371285045090391815]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 48780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 48700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490278086082309, 362490312429419921⟩, ⟨(-258245396973259207), (-257113102444284333)⟩, true⟩

def words09 : List Nat := [371285044663167311, 371285044588933688, 371285044778838267, 371285044780464834, 371285044574354572, 371285044296893349, 371285044018805425, 371285043918085810, 371285043716453096, 371285043826267439]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 48790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 48700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 48700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk487
