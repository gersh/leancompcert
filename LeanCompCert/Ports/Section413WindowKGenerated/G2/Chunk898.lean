import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk898

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360564591620627135, 360564644617747032⟩, ⟨1557394451674123147, 1560608220632911839⟩, true⟩

def state01 : KState := ⟨⟨360586232972713665, 360586285982077846⟩, ⟨(-386146583274068511), (-382931714716907651)⟩, true⟩

def words00 : List Nat := [360582023135967028, 360582023038089540, 360582023001656788, 360582022962554311, 360582022923336965, 360582022779059956, 360582022542166962, 360582022381607751, 360582022220671429, 360582022231371175]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 89800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 89800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360564698577013616, 360564751598725954⟩, ⟨1547944388575747271, 1551160366181343829⟩, true⟩

def words01 : List Nat := [360582022232539481, 360582022191777730, 360582022150771699, 360582022129980678, 360582022131074020, 360582022040617221, 360582021950047325, 360582021759041136, 360582021443994225, 360582021253214725]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 89810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 89800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574826608937257, 360574879642851544⟩, ⟨638169669807364097, 641386743453226817⟩, true⟩

def words02 : List Nat := [360582021061994663, 360582020994840226, 360582020838317503, 360582020611595201, 360582020384645111, 360582020126382862, 360582019962593308, 360582019878493129, 360582019794261927, 360582019648901341]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 89820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 89800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583750279803719, 360583803325966088⟩, ⟨(-163567058689452850), (-160348884740404706)⟩, true⟩

def words03 : List Nat := [360582019570484919, 360582019453345056, 360582019341042026, 360582019342338059, 360582019224991144, 360582019003829289, 360582018782430299, 360582018580309990, 360582018497323062, 360582018518531394]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 89830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 89800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360570227440545767, 360570280499043942⟩, ⟨1051287843476514913, 1054507125735496029⟩, true⟩

def words04 : List Nat := [360582018519686120, 360582018478667586, 360582018371222584, 360582018301207592, 360582018230872251, 360582018045321367, 360582017764390821, 360582017403500144, 360582017042360182, 360582016805396035]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 89840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 89800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360543115354065691, 360543168424789576⟩, ⟨3487491753997089921, 3490712134798851833⟩, true⟩

def words05 : List Nat := [360582016675826440, 360582016601058054, 360582016526127557, 360582016379460995, 360582016108885932, 360582015807520110, 360582015505758727, 360582015288021578, 360582014973428973, 360582014542470401]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 89850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 89800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575899992354623, 360575953075318634⟩, ⟨541292314190375050, 544513794948800082⟩, true⟩

def words06 : List Nat := [360582014111228732, 360582013738680139, 360582013452215741, 360582013258696468, 360582013065091535, 360582012764833658, 360582012477921343, 360582012315071890, 360582012151850938, 360582011980347552]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 89860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 89800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360554617965842791, 360554671061161877⟩, ⟨2454016697028019747, 2457239288198098081⟩, true⟩

def words07 : List Nat := [360582011914086015, 360582011772426309, 360582011630539445, 360582011449695807, 360582011330813671, 360582011178853305, 360582011026754864, 360582010812684537, 360582010474739043, 360582010172067508]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 89870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 89800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360549184804069177, 360549237911592084⟩, ⟨2942357200782143302, 2945580888893622510⟩, true⟩

def words08 : List Nat := [360582009868952759, 360582009584986534, 360582009265292442, 360582008882394011, 360582008499290570, 360582008085416179, 360582007745004552, 360582007401922988, 360582007058709837, 360582006638801937]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 89880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 89800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588093429726055, 360588146549493148⟩, ⟨(-555355067104396150), (-552130278303162878)⟩, true⟩

def words09 : List Nat := [360582006275311735, 360582006035843634, 360582005795976608, 360582005658891174, 360582005524644714, 360582005284994804, 360582005045098009, 360582004929179343, 360582004943271100, 360582005012932897]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 89890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 89800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 89800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk898
