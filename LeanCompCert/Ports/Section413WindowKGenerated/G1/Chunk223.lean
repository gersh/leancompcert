import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk223

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473151583875704, 362473158304581589⟩, ⟨243326311283527004, 243427658331165878⟩, true⟩

def state01 : KState := ⟨⟨362522696627196101, 362522703354164003⟩, ⟨(-861608819496828177), (-861507332775480655)⟩, true⟩

def words00 : List Nat := [371284074843323754, 371284075112090295, 371284077390169918, 371284079668339765, 371284081619496467, 371284081620195833, 371284083421866623, 371284085327803600, 371284088053898986, 371284089785396334]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 22300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 22300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362505378456502888, 362505385189839124⟩, ⟨(-475039392282842551), (-474937763452189067)⟩, true⟩

def words01 : List Nat := [371284091189408858, 371284092593530995, 371284095665748295, 371284097741521563, 371284100427993343, 371284103114497126, 371284105724980290, 371284105725678623, 371284106615326441, 371284107569506156]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 22310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 22300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362470473966610681, 362470480706175250⟩, ⟨304051664706016908, 304153432585556778⟩, true⟩

def words02 : List Nat := [371284109187736140, 371284109188434571, 371284108133596788, 371284106701377111, 371284105269027663, 371284104229603292, 371284102248948401, 371284102021493530, 371284101793823675, 371284101549551227]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 22320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 22300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362529260655757530, 362529267401625826⟩, ⟨(-1008917871261350274), (-1008815962586966916)⟩, true⟩

def words03 : List Nat := [371284102008096750, 371284103076851207, 371284105550720779, 371284106119026511, 371284106363199575, 371284106607577257, 371284107670627628, 371284107994733259, 371284110016667863, 371284112038724123]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 22330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 22300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487064852247972, 362487071604421795⟩, ⟨(-66235372125875185), (-66133322554147367)⟩, true⟩

def words04 : List Nat := [371284113710211634, 371284113710910819, 371284113719392730, 371284114725211782, 371284116040440917, 371284116041140190, 371284114689173624, 371284113332050344, 371284112618274971, 371284112751459774]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 22340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 22300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362443643616437150, 362443650374926808⟩, ⟨904486648785417657, 904588839547543965⟩, true⟩

def words05 : List Nat := [371284113504113962, 371284114256989348, 371284114999549044, 371284115000248474, 371284113077373380, 371284111292125215, 371284109506674598, 371284109505875724, 371284107856109779, 371284106047536269]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 22350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 22300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469163327472361, 362469170092218125⟩, ⟨333766424293150377, 333868754974495403⟩, true⟩

def words06 : List Nat := [371284104238805055, 371284104024673307, 371284102818818583, 371284102218724323, 371284101618487758, 371284100526301686, 371284097129915380, 371284095732577693, 371284094935256718, 371284094935980955]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 22360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 22300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362456787417307557, 362456794188430809⟩, ⟨610830762924221189, 610933236302367991⟩, true⟩

def words07 : List Nat := [371284094269353406, 371284093592043898, 371284093555886029, 371284093572962151, 371284094154633650, 371284094736525427, 371284095307560670, 371284095308260941, 371284093585951138, 371284092366996599]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 22370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 22300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362451879815423357, 362451886592788004⟩, ⟨720846207593410910, 720948820686103048⟩, true⟩

def words08 : List Nat := [371284091924338013, 371284091925040357, 371284090931946735, 371284089926005786, 371284088919882420, 371284087827443843, 371284086298299978, 371284086354454877, 371284086354980593, 371284086182814182]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 22380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 22300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362500533583003737, 362500540366720084⟩, ⟨(-368739894359872391), (-368637139021101465)⟩, true⟩

def words09 : List Nat := [371284085301979230, 371284085859528842, 371284087241024984, 371284087241725828, 371284085967029955, 371284084379296498, 371284083196995526, 371284083197767386, 371284083350774045, 371284084086240592]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 22390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 22300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 22300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk223
