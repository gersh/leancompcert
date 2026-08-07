import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk656

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602630284489461, 360602657877198391⟩, ⟨(-1297077275851699102), (-1295854554617793136)⟩, true⟩

def state01 : KState := ⟨⟨360581406991837863, 360581434593357675⟩, ⟨95107509522346949, 96330808792267825⟩, true⟩

def words00 : List Nat := [360582904452872109, 360582904453796616, 360582904376906600, 360582904356744164, 360582904336312736, 360582904257783967, 360582903947411818, 360582903496637462, 360582903045699677, 360582902826992674]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 65600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 65600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360555954488723625, 360555982098960767⟩, ⟨1765112837906513136, 1766336709164148812⟩, true⟩

def words01 : List Nat := [360582902805379335, 360582902670392328, 360582902535308384, 360582902284119971, 360582901876220310, 360582901316083733, 360582900755693103, 360582900427363052, 360582900166078349, 360582899756826725]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 65610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 65600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598554165198504, 360598581784163386⟩, ⟨(-1030482162762681308), (-1029257718747488512)⟩, true⟩

def words02 : List Nat := [360582899347375592, 360582899126131636, 360582899100210415, 360582899180370689, 360582899181239346, 360582899041785682, 360582898972801355, 360582898922026837, 360582899050938150, 360582899290848528]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 65620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 65600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585961488817468, 360585989116599089⟩, ⟨(-203904786138020542), (-202679763436879836)⟩, true⟩

def words03 : List Nat := [360582899395987627, 360582899501240447, 360582899838045780, 360582900291381056, 360582900686243544, 360582901081245031, 360582901266445151, 360582901319974840, 360582901367777108, 360582901415871848]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 65630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 65600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360601773279465891, 360601800915960526⟩, ⟨(-1241926340439257629), (-1240700745772730061)⟩, true⟩

def words04 : List Nat := [360582901601780296, 360582901684422403, 360582901685246545, 360582901651796799, 360582901618198936, 360582901515115707, 360582901786015585, 360582902057090552, 360582902198382305, 360582902487211951]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 65640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 65600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360618132392365299, 360618160037599796⟩, ⟨(-2315982543085124262), (-2314756374603783814)⟩, true⟩

def words05 : List Nat := [360582903007440045, 360582903527923607, 360582904006828095, 360582904409696197, 360582904613802904, 360582904817968262, 360582905253542746, 360582905822822326, 360582906360496459, 360582906898375542]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 65650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 65600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587903581605356, 360587931235650477⟩, ⟨(-331157648813506709), (-329930901782870031)⟩, true⟩

def words06 : List Nat := [360582907299009869, 360582907468419777, 360582907706394332, 360582907944642087, 360582908055414412, 360582908056339790, 360582907935873679, 360582907620960107, 360582907305879069, 360582907238729723]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 65660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 65600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569881080966304, 360569908743718827⟩, ⟨852520965567148537, 853748284457517559⟩, true⟩

def words07 : List Nat := [360582907394919049, 360582907551278799, 360582907590913754, 360582907636941791, 360582907637717836, 360582907556574378, 360582907624445702, 360582907625371288, 360582907544272012, 360582907347318972]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 65670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 65600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360567618850500764, 360567646522007624⟩, ⟨1001095774164506580, 1002323668081670776⟩, true⟩

def words08 : List Nat := [360582907150180508, 360582906830556791, 360582906662765686, 360582906595582038, 360582906528329271, 360582906254597425, 360582905749530968, 360582905476151060, 360582905202490231, 360582904912448813]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 65680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 65600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360563807247063981, 360563834927386806⟩, ⟨1251491190272706429, 1252719663353707437⟩, true⟩

def words09 : List Nat := [360582904681007080, 360582904329879204, 360582903978578623, 360582903815217619, 360582903767588386, 360582903560849886, 360582903354016950, 360582903007710553, 360582902486911940, 360582902197757487]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 65690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 65600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 65600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk656
