import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk386

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362499949947196071, 362499971028800765⟩, ⟨(-573274233525494681), (-572724324462954081)⟩, true⟩

def state01 : KState := ⟨⟨362482209416701346, 362482230509702913⟩, ⟨111491979643161942, 112042328681869668⟩, true⟩

def words00 : List Nat := [371285134382493252, 371285134383755729, 371285134040485496, 371285134205153998, 371285134407091035, 371285134408353764, 371285133801693630, 371285133114095413, 371285132426000838, 371285132408917673]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 38600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 38600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362461172530943734, 362461193635298181⟩, ⟨923992385214012589, 924543172646901959⟩, true⟩

def words01 : List Nat := [371285132929791787, 371285133526317528, 371285134077157845, 371285134078421144, 371285133854363155, 371285133835414570, 371285134225949321, 371285134227212213, 371285133745563671, 371285133127080856]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 38610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 38600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485230993190568, 362485252108855350⟩, ⟨(-5252283662586083), (-4701059368095993)⟩, true⟩

def words02 : List Nat := [371285132508087121, 371285132228808009, 371285131653243231, 371285131525156173, 371285131396662815, 371285131149916695, 371285130457633659, 371285130220263577, 371285130413026291, 371285130417483962]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 38620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 38600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483023087787113, 362483044214992890⟩, ⟨80057206426504654, 80608876605520442⟩, true⟩

def words03 : List Nat := [371285130418428781, 371285130398310254, 371285130632143509, 371285130633535529, 371285130789205229, 371285130970154454, 371285131139598132, 371285131140861788, 371285130418424062, 371285130366043758]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 38630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 38600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362450243644552126, 362450264783002995⟩, ⟨1346845435241638278, 1347397539990372794⟩, true⟩

def words04 : List Nat := [371285130677870331, 371285130679134074, 371285130191769287, 371285129579472111, 371285128966735301, 371285128454332810, 371285127711191525, 371285127244630180, 371285126777660393, 371285126297621116]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 38640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 38600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362507357772022532, 362507378921880426⟩, ⟨(-860840825206210514), (-860288279517601360)⟩, true⟩

def words05 : List Nat := [371285125396522793, 371285125165010150, 371285125368748928, 371285125435828459, 371285125436815923, 371285125395094535, 371285125647969271, 371285125672517498, 371285126248990184, 371285126825982297]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 38650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 38600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474199444935850, 362474220606215515⟩, ⟨421120865359347806, 421673852672297398⟩, true⟩

def words06 : List Nat := [371285127265603732, 371285127266874100, 371285127217857295, 371285127371188277, 371285127480609335, 371285127481873867, 371285126700793473, 371285125919371546, 371285125137464641, 371285125024438228]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 38660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 38600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362462018950107901, 362462040122776296⟩, ⟨892315421346109099, 892868849120086305⟩, true⟩

def words07 : List Nat := [371285125129561047, 371285125517172978, 371285125906243314, 371285125907508365, 371285125507106175, 371285125045361162, 371285124787842288, 371285124789107410, 371285124194074414, 371285123598710115]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 38670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 38600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479616524664630, 362479637708680227⟩, ⟨211674745064120192, 212228611804349050⟩, true⟩

def words08 : List Nat := [371285123002803885, 371285122962597493, 371285122967975158, 371285123252293940, 371285123427491450, 371285123428759540, 371285123015730231, 371285122941984596, 371285123068233605, 371285123069543612]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 38680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 38600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362501302022564131, 362501323218098469⟩, ⟨(-627443000479781645), (-626888688021044769)⟩, true⟩

def words09 : List Nat := [371285122928725914, 371285122777738306, 371285123141325858, 371285123324319653, 371285123673138002, 371285124022456922, 371285124370416362, 371285124371690424, 371285124542420870, 371285124962548973]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 38690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 38600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 38600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk386
