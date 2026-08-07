import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk134

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360733821558912465, 360733822563430378⟩, ⟨(-2036638280009765289), (-2036629163495517203)⟩, true⟩

def state01 : KState := ⟨⟨360511336783078626, 360511337789176123⟩, ⟨945373934086286863, 945383071774919401⟩, true⟩

def words00 : List Nat := [360581855160868685, 360581858141144891, 360581862684336438, 360581867226897722, 360581867873699507, 360581867873865434, 360581862996783245, 360581854664043091, 360581846332515367, 360581836153961725]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 13400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 13400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360424099942322958, 360424100949986914⟩, ⟨2116135450439428484, 2116144609142085936⟩, true⟩

def words01 : List Nat := [360581831179309565, 360581831461406430, 360581831461554801, 360581827790490108, 360581821996291508, 360581814754518316, 360581807513775564, 360581805807857728, 360581798588173200, 360581786837404358]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 13410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 13400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360630757234914724, 360630758244145976⟩, ⟨(-658155514176349092), (-658146334432764052)⟩, true⟩

def words02 : List Nat := [360581775088348296, 360581768872334706, 360581765481581519, 360581765214333934, 360581764947113291, 360581759963416378, 360581755585735356, 360581754055182652, 360581752560099264, 360581756208971175]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 13420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 13400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360490761604070943, 360490762614886542⟩, ⟨1222505816243906654, 1222515017273392058⟩, true⟩

def words03 : List Nat := [360581756209120343, 360581755091865294, 360581753974747325, 360581750494298913, 360581749829679589, 360581747727723057, 360581745626062629, 360581740722670033, 360581730321910025, 360581723553671765]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 13430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 13400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360531023711888119, 360531024724270263⟩, ⟨681566053064139881, 681575275155844867⟩, true⟩

def words04 : List Nat := [360581716786383034, 360581716683356670, 360581716683504920, 360581715047724667, 360581713412160725, 360581710346174243, 360581710204160367, 360581707551552878, 360581704899321689, 360581699465917538]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 13440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 13400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360717112376495661, 360717113390449077⟩, ⟨(-1822360300299192689), (-1822351057066081999)⟩, true⟩

def words05 : List Nat := [360581697435726405, 360581699172684409, 360581701660006419, 360581705323929626, 360581705324085359, 360581703844717718, 360581706385437303, 360581713207582557, 360581723267166444, 360581733325292991]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 13450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 13400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360691770687159789, 360691771702702089⟩, ⟨(-1481792703218749025), (-1481783438591403529)⟩, true⟩

def words06 : List Nat := [360581739111992072, 360581741770788563, 360581749923810237, 360581758075672604, 360581764802655463, 360581766053256070, 360581766053404627, 360581764041444956, 360581765508110764, 360581773674449443]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 13460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 13400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360548420677047994, 360548421694158509⟩, ⟨449918364543066065, 449927650302237795⟩, true⟩

def words07 : List Nat := [360581784120632297, 360581794565295906, 360581802201807630, 360581804365636654, 360581804365779709, 360581801514756468, 360581801297168456, 360581801592220328, 360581801592368916, 360581799116287756]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 13470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 13400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360644222777077519, 360644223795765833⟩, ⟨(-842016855751766178), (-842007548716231150)⟩, true⟩

def words08 : List Nat := [360581796640537592, 360581792684332864, 360581796342661557, 360581800000479386, 360581800000633393, 360581799010607190, 360581801199308060, 360581805030789327, 360581806631121612, 360581811257872702]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 13480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 13400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360679543322451862, 360679544342731996⟩, ⟨(-1318790435978731888), (-1318781107461647516)⟩, true⟩

def words09 : List Nat := [360581813106190220, 360581814954250607, 360581820406033608, 360581829373842819, 360581836929204037, 360581844483475658, 360581847845007965, 360581849616316451, 360581856853098194, 360581864088864754]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 13490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 13400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 13400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk134
