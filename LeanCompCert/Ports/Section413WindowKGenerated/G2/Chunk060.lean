import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk060

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360503747566744983, 360503747752594543⟩, ⟨401300223509623610, 401300980178629552⟩, true⟩

def state01 : KState := ⟨⟨360503606118612103, 360503606305110417⟩, ⟨401213766450351921, 401214527015108433⟩, true⟩

def words00 : List Nat := [360570620103955094, 360570616810814375, 360570586094229817, 360570534895235947, 360570483713283017, 360570425191894449, 360570392847082966, 360570387977168083, 360570383108866632, 360570364129904945]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 6000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 6000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360642012876057366, 360642013063207767⟩, ⟨(-431324787224670826), (-431324022737607922)⟩, true⟩

def words01 : List Nat := [360570369351655794, 360570385673939568, 360570400732466560, 360570404392037030, 360570404392100598, 360570384631572296, 360570364877599568, 360570352650595504, 360570364554374794, 360570376454216303]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 6010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 6000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360513029908499786, 360513030096308184⟩, ⟨344009270451806047, 344010038903248891⟩, true⟩

def words02 : List Nat := [360570376454278476, 360570372883389648, 360570342082954531, 360570322074404617, 360570302072478663, 360570274006062374, 360570236423446071, 360570175130726515, 360570113858326125, 360570079854003582]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 6020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 6000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360269783884948458, 360269784073408244⟩, ⟨1812857210309874483, 1812857982692499639⟩, true⟩

def words03 : List Nat := [360570073666783900, 360570076937912142, 360570076937973775, 360570066230322396, 360570057282658992, 360570030086619254, 360570002899569444, 360570002897642028, 360569975824072316, 360569926123522897]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 6030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 6000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360568657420490455, 360568657609605861⟩, ⟨5826662170939774, 5827438516752524⟩, true⟩

def words04 : List Nat := [360569876439413444, 360569825638130837, 360569792470931252, 360569786438036327, 360569780407132333, 360569751654127273, 360569695879804335, 360569667215356237, 360569638560363722, 360569620822583837]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 6040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 6000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360595784738613270, 360595784928389285⟩, ⟨(-158470894119351246), (-158470113773511254)⟩, true⟩

def words05 : List Nat := [360569620663463284, 360569606662251778, 360569605705003726, 360569632734496439, 360569640494223869, 360569648251399353, 360569648251461869, 360569642401328966, 360569634744519313, 360569639059098160]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 6050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 6000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360531732801449338, 360531732991882023⟩, ⟨229472905094921852, 229473689423478436⟩, true⟩

def words06 : List Nat := [360569639059155105, 360569631205331663, 360569624985166470, 360569601395057326, 360569577812716083, 360569546958090770, 360569540942318649, 360569551393761145, 360569551393824446, 360569537553566287]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 6060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 6000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360771177785816518, 360771177976907450⟩, ⟨(-1225886934107291487), (-1225886145779976153)⟩, true⟩

def words07 : List Nat := [360569532564321377, 360569533801762430, 360569561906309273, 360569563261913857, 360569563261978808, 360569541597272587, 360569519939682120, 360569518798331495, 360569551966016136, 360569585122807800]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 6070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 6000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582324069332260, 360582324261089150⟩, ⟨(-78957245317505744), (-78956452937882950)⟩, true⟩

def words08 : List Nat := [360569604531377564, 360569604531447349, 360569597259756714, 360569574356166570, 360569551460085187, 360569521375138953, 360569484423396156, 360569433800405597, 360569383194029575, 360569361454827800]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 6080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 6000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360197559864149565, 360197560056565327⟩, ⟨2267715562527576793, 2267716358923118497⟩, true⟩

def words09 : List Nat := [360569390296021226, 360569419127760900, 360569434564344080, 360569447217867712, 360569447217926475, 360569443515256633, 360569439813782478, 360569422054032452, 360569377790370976, 360569316836716658]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 6090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 6000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 6000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk060
