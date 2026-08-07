import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk805

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360562916281292906, 360562958510386721⟩, ⟨1543081442870455670, 1545377335239104604⟩, true⟩

def state01 : KState := ⟨⟨360556712583099726, 360556754823055693⟩, ⟨2042583572122253603, 2044880338948496775⟩, true⟩

def words00 : List Nat := [360582155506824033, 360582155385467208, 360582155346935578, 360582155354047169, 360582155355119413, 360582155232251716, 360582154955202814, 360582154623477244, 360582154291432649, 360582153908125231]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 80500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 80500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360562474997451043, 360562517248373770⟩, ⟨1578631161392774659, 1580928811205671823⟩, true⟩

def words01 : List Nat := [360582153593678356, 360582153188587216, 360582152783281841, 360582152532408946, 360582152407103065, 360582152243544970, 360582152079865498, 360582151839244702, 360582151480103818, 360582151237583975]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 80510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 80500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360566403111466886, 360566445373246619⟩, ⟨1262296567170453815, 1264595091244162855⟩, true⟩

def words02 : List Nat := [360582150994694604, 360582150748229155, 360582150529976774, 360582150213716758, 360582149897277414, 360582149540739708, 360582149261012619, 360582149135518893, 360582149009885564, 360582148776838376]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 80520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 80500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582200860272776, 360582243132921992⟩, ⟨(-10040995823948876), (-7741596377266148)⟩, true⟩

def words03 : List Nat := [360582148582777790, 360582148412712661, 360582148242302502, 360582148156602498, 360582147965380019, 360582147627614803, 360582147289637345, 360582147105956251, 360582147010592145, 360582147012978395]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 80530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 80500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588832974236886, 360588875257891110⟩, ⟨(-544245777388048164), (-541945491546278160)⟩, true⟩

def words04 : List Nat := [360582147014018019, 360582146916052114, 360582147006129426, 360582147113853930, 360582147161571777, 360582147239062676, 360582147240089516, 360582147240575155, 360582147240851376, 360582147278206857]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 80540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 80500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360571982127968720, 360572024422468196⟩, ⟨813207442062265169, 815508601543714577⟩, true⟩

def words05 : List Nat := [360582147487935324, 360582147697879283, 360582147791452972, 360582147792605483, 360582147732297919, 360582147633900454, 360582147589327176, 360582147590480091, 360582147543475145, 360582147419011688]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575990586056648, 360576032891455088⟩, ⟨490232896188356928, 492534933743484294⟩, true⟩

def words06 : List Nat := [360582147294291675, 360582147229275613, 360582147230226313, 360582147181116627, 360582147131911488, 360582146938091287, 360582146590285608, 360582146396670732, 360582146202711327, 360582146022071242]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360562740945824577, 360562783262198419⟩, ⟨1557856894630179479, 1560159816527256387⟩, true⟩

def words07 : List Nat := [360582145947225977, 360582145785887022, 360582145624331337, 360582145656479688, 360582145657452278, 360582145623085712, 360582145588622139, 360582145434829413, 360582145127079441, 360582144888117100]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563512796795443, 360563555124023475⟩, ⟨1495647149200788360, 1497950945782852528⟩, true⟩

def words08 : List Nat := [360582144648774079, 360582144519474822, 360582144293946049, 360582143991634269, 360582143689122102, 360582143319446678, 360582143081810505, 360582142890023611, 360582142698115918, 360582142429468107]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569166153448870, 360569208491584134⟩, ⟨1039935666054082636, 1042240341701127726⟩, true⟩

def words09 : List Nat := [360582142199780001, 360582141919179232, 360582141638245056, 360582141476304892, 360582141211236106, 360582140819463357, 360582140427488402, 360582139985644026, 360582139672427993, 360582139513193330]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk805
