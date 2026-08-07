import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk504

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579098638568621, 360579114584352291⟩, ⟨142657203044795793, 143200243824553439⟩, true⟩

def state01 : KState := ⟨⟨360568523036382082, 360568538988716803⟩, ⟨675744040330435099, 676287411315875349⟩, true⟩

def words00 : List Nat := [360581955863108955, 360581956032960841, 360581956033580926, 360581955979496003, 360581955925301270, 360581955628952399, 360581955556071698, 360581955346608568, 360581955137084012, 360581954727881967]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 50400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 50400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360627716092957386, 360627732051859564⟩, ⟨(-2308510701283464753), (-2307966999198952409)⟩, true⟩

def words01 : List Nat := [360581954589058015, 360581954716560291, 360581954903430570, 360581955258205921, 360581955276273032, 360581955294394865, 360581955705156325, 360581956311287239, 360581957219738708, 360581958128311857]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 50410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 50400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360633154495094964, 360633170460636953⟩, ⟨(-2582902503348382832), (-2582358466451802114)⟩, true⟩

def words02 : List Nat := [360581958734379026, 360581959213694299, 360581960085536740, 360581960957553840, 360581961725862131, 360581962323771669, 360581962668795780, 360581963013885636, 360581963668915682, 360581964685093105]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 50420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 50400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565586363200460, 360565602335299147⟩, ⟨824962675712687392, 825507043296206626⟩, true⟩

def words03 : List Nat := [360581965695564870, 360581966706129011, 360581967519567183, 360581968047915694, 360581968208568830, 360581968369393760, 360581968769370571, 360581968777443554, 360581968778066780, 360581968454317708]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 50430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 50400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360613377449493404, 360613393428172846⟩, ⟨(-1585753862209804231), (-1585209162660223877)⟩, true⟩

def words04 : List Nat := [360581968198340728, 360581968570034705, 360581969232645134, 360581969895362647, 360581970208025528, 360581970463690462, 360581970991279891, 360581971519052545, 360581972036714344, 360581972660246339]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 50440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 50400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360596625856928512, 360596641842240487⟩, ⟨(-740569853520328328), (-740024819326641390)⟩, true⟩

def words05 : List Nat := [360581973039458439, 360581973418731548, 360581973914080861, 360581974604173972, 360581975195468239, 360581975786866833, 360581976077832214, 360581976078529017, 360581976268331460, 360581976559758439]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 50450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 50400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360619756733670979, 360619772725555809⟩, ⟨(-1907927653759290549), (-1907382287867601067)⟩, true⟩

def words06 : List Nat := [360581977242970314, 360581977745219285, 360581977936413305, 360581978127660146, 360581978220295211, 360581978558712866, 360581979213853517, 360581979869107213, 360581980327598359, 360581981077126660]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 50460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 50400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360605885359864990, 360605901358323637⟩, ⟨(-1207736209560289858), (-1207190511854982294)⟩, true⟩

def words07 : List Nat := [360581982056759496, 360581983036564676, 360581984150058113, 360581984872131485, 360581985264751793, 360581985657410217, 360581986040201597, 360581986649691340, 360581987124007575, 360581987598456460]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 50470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 50400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582188382187992, 360582204387291057⟩, ⟨(-11572232626547324), (-11026199480164458)⟩, true⟩

def words08 : List Nat := [360581987831681392, 360581987832378732, 360581987996390390, 360581988163308158, 360581988163892400, 360581988120201368, 360581987685090657, 360581987053663791, 360581986422128969, 360581986007788173]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 50480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 50400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360556386551217564, 360556402562887693⟩, ⟨1291252232205767928, 1291798596957049864⟩, true⟩

def words09 : List Nat := [360581986008361637, 360581986003787365, 360581985999133870, 360581985798261895, 360581985206031822, 360581984515792908, 360581983825377010, 360581983526481528, 360581983238949919, 360581982733124467]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 50490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 50400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 50400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk504
