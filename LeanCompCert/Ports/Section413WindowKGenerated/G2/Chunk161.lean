import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk161

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360784660769244975, 360784662244377776⟩, ⟨(-3270250091212990980), (-3270234012047689134)⟩, true⟩

def state01 : KState := ⟨⟨360743965906039569, 360743967383101239⟩, ⟨(-2615236055421555327), (-2615219945191858573)⟩, true⟩

def words00 : List Nat := [360581565432841575, 360581573862359443, 360581586141686233, 360581598419548613, 360581609685618697, 360581617127854140, 360581621258721631, 360581625389094544, 360581632190739882, 360581642267019565]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 16100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 16100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360674719936927927, 360674721415898646⟩, ⟨(-1498938919353971841), (-1498922778359985259)⟩, true⟩

def words01 : List Nat := [360581656188373868, 360581670108039344, 360581681521983266, 360581693077387055, 360581702145160292, 360581711211861210, 360581722696479766, 360581730362812162, 360581736131670400, 360581741899841331]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 16110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 16100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360790104842728820, 360790106323615785⟩, ⟨(-3359816975189505336), (-3359800803295943440)⟩, true⟩

def words02 : List Nat := [360581747002153862, 360581754044532129, 360581762788386164, 360581771531194352, 360581776911958178, 360581781793710840, 360581790513846465, 360581799232965662, 360581811171310727, 360581824084244640]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 16120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 16100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360675503088387397, 360675504571205343⟩, ⟨(-1510830894477925036), (-1510814691427851618)⟩, true⟩

def words03 : List Nat := [360581834712485206, 360581845339430140, 360581854917398273, 360581866427889694, 360581875302167134, 360581884175374961, 360581889946970389, 360581891912564205, 360581897712769318, 360581903512322508]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 16130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 16100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360774233084442559, 360774234569176738⟩, ⟨(-3104793541897254594), (-3104777307909979816)⟩, true⟩

def words04 : List Nat := [360581913145509277, 360581922912211408, 360581930726412404, 360581938539667597, 360581945344032286, 360581954962140074, 360581967056169545, 360581979148741272, 360581988296029793, 360582000199298094]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 16140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 16100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360805267187242020, 360805268673892870⟩, ⟨(-3606072839682517121), (-3606056574731336355)⟩, true⟩

def words05 : List Nat := [360582014267120231, 360582028333259589, 360582044291020114, 360582058206542372, 360582068797069853, 360582079386304093, 360582092631101932, 360582107798788088, 360582121608414548, 360582135416375926]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 16150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 16100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360653873928548808, 360653875417138983⟩, ⟨(-1159258722901854599), (-1159242426602019025)⟩, true⟩

def words06 : List Nat := [360582147278124354, 360582155345925789, 360582163282664641, 360582171218479975, 360582177352732467, 360582181346715768, 360582182685786552, 360582184024713585, 360582184481428692, 360582188914968306]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 16160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 16100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360490419883048972, 360490421373552798⟩, ⟨1484962375340767412, 1484978702594240744⟩, true⟩

def words07 : List Nat := [360582195898832551, 360582202881872866, 360582207847577573, 360582209025789927, 360582209205600514, 360582209385442259, 360582209438122927, 360582209438326495, 360582205705043465, 360582200032551206]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 16170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 16100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360625428397237689, 360625429889663827⟩, ⟨(-700260823969241456), (-700244465603315908)⟩, true⟩

def words08 : List Nat := [360582194360715434, 360582189199624506, 360582187629173283, 360582188750017525, 360582188750206099, 360582186622700546, 360582180712246027, 360582178612732828, 360582178223881562, 360582180895432260]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 16180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 16100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360675066837341278, 360675068331712344⟩, ⟨(-1504381891406756298), (-1504365501542808584)⟩, true⟩

def words09 : List Nat := [360582180895618568, 360582180557350324, 360582183688964061, 360582189071300758, 360582192437541208, 360582195803399095, 360582197235470936, 360582200530735959, 360582206263481298, 360582211995588475]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 16190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 16100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 16100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk161
