import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk066

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360997877596008401, 360997877823101792⟩, ⟨(-2771943026326656934), (-2771942009602231384)⟩, true⟩

def state01 : KState := ⟨⟨360830018460287059, 360830018688102454⟩, ⟨(-1664443079559145777), (-1664442058065789109)⟩, true⟩

def words00 : List Nat := [360578001898784081, 360578031097590448, 360578046247571168, 360578061392973093, 360578070612442796, 360578091840958497, 360578135802523168, 360578179750800062, 360578212022657716, 360578250111780296]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 6600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 6600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360866677879431363, 360866678107970797⟩, ⟨(-1907839365570772887), (-1907838339287923591)⟩, true⟩

def words01 : List Nat := [360578290799756547, 360578331475449296, 360578378951065792, 360578404041965269, 360578407513888112, 360578410984765715, 360578420557906033, 360578441464939334, 360578485005279978, 360578528532485535]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 6610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 6600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360806961321686825, 360806961550958852⟩, ⟨(-1512420303132857840), (-1512419271996669422)⟩, true⟩

def words02 : List Nat := [360578560455545170, 360578607444974562, 360578665697927548, 360578723933317702, 360578773734392131, 360578801216786796, 360578815814504817, 360578830407826985, 360578844013616529, 360578878415384027]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 6620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 6600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360553267312556750, 360553267542552720⟩, ⟨171194082397786455, 171195118337397633⟩, true⟩

def words03 : List Nat := [360578921407502439, 360578964386672231, 360578988588423093, 360579001731978770, 360579009066861983, 360579016399556409, 360579046223954536, 360579053823220535, 360579053823289118, 360579049939892690]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 6630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 6600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360561144863021983, 360561145093746664⟩, ⟨118483198102200780, 118484238883984090⟩, true⟩

def words04 : List Nat := [360579052503024245, 360579072939944067, 360579082235362419, 360579091527996859, 360579091528067865, 360579081485688540, 360579049269970426, 360579015723092926, 360578982186284045, 360578962272526211]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 6640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 6600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360497458650300761, 360497458881760116⟩, ⟨542458127957775766, 542459173628880350⟩, true⟩

def words05 : List Nat := [360578959593723397, 360578945413346889, 360578939449394491, 360578958831876756, 360578963685316126, 360578968537309795, 360578968537379709, 360578956036596265, 360578921439657595, 360578909208130819]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 6650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 6600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360550112950178494, 360550113182365831⟩, ⟨191128017658698721, 191129068181757585⟩, true⟩

def words06 : List Nat := [360578907104320271, 360578907104397501, 360578895138604029, 360578871739613987, 360578848347631518, 360578812958374496, 360578795985915969, 360578791922254234, 360578787859803884, 360578768215076740]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 6660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 6600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360774521888444838, 360774522121363063⟩, ⟨(-1307586330627709111), (-1307585275226009031)⟩, true⟩

def words07 : List Nat := [360578763919677619, 360578758628027477, 360578770311974256, 360578776496487030, 360578776496558388, 360578763253240604, 360578750013875406, 360578746514808220, 360578775822596486, 360578805121628591]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 6670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 6600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360656160109694894, 360656160343350658⟩, ⟨(-517701959803691805), (-517700899471516803)⟩, true⟩

def words08 : List Nat := [360578818210591318, 360578826038386532, 360578844539066667, 360578863034234173, 360578865505324494, 360578865505402053, 360578846039547429, 360578815312811661, 360578784595247832, 360578787618874270]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 6680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 6600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360345426658195028, 360345426892583489⟩, ⟨1563459235137513456, 1563460300375102606⟩, true⟩

def words09 : List Nat := [360578821340889540, 360578855052844012, 360578872905633487, 360578872905711133, 360578868847710975, 360578851067014583, 360578833291605014, 360578826771653890, 360578814010039158, 360578779176221565]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 6690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 6600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 6600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk066
