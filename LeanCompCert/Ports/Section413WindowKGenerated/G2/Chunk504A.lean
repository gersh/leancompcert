import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk504A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk504A
