import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk041

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨361013182824771435, 361013182908019437⟩, ⟨(-1821990976693708304), (-1821990744858714550)⟩, true⟩

def state01 : KState := ⟨⟨360662856730630031, 360662856814311462⟩, ⟨(-384775219434029591), (-384774985819805115)⟩, true⟩

def words00 : List Nat := [360568981050393713, 360569061719827484, 360569148481185349, 360569235200285528, 360569305378864319, 360569317733066532, 360569317733107153, 360569292301042448, 360569266881348363, 360569260369208129]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 4100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 4100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360667759605936461, 360667759690046754⟩, ⟨(-403599635178346494), (-403599399799313822)⟩, true⟩

def words01 : List Nat := [360569341767665310, 360569423126549983, 360569474357862573, 360569542630560031, 360569594592133033, 360569646528476232, 360569720899868172, 360569774887871240, 360569798670630887, 360569822441854735]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 4110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 4100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360946100262785806, 360946100347327684⟩, ⟨(-1553489246512860232), (-1553489009353548544)⟩, true⟩

def words02 : List Nat := [360569860825320515, 360569931213999564, 360569975138012465, 360570019040736765, 360570019040779196, 360570005092890495, 360569933882125337, 360569920841631418, 360569952887387822, 360570043942255414]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 4120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 4100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360937396608261908, 360937396693239765⟩, ⟨(-1517413507695122449), (-1517413268733067499)⟩, true⟩

def words03 : List Nat := [360570094385912085, 360570144805162989, 360570253223803314, 360570401122554274, 360570532942612881, 360570664698951793, 360570752505031918, 360570783195026556, 360570871749048815, 360570960260317025]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 4130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 4100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360719019892758707, 360719019978168887⟩, ⟨(-612101847160307770), (-612101606406238604)⟩, true⟩

def words04 : List Nat := [360571073150094714, 360571166204335128, 360571229350099794, 360571292465401776, 360571339761838496, 360571416259236755, 360571462529524783, 360571508777516867, 360571525615131901, 360571561147427804]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 4140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 4100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361343064231950283, 361343064317795569⟩, ⟨(-3206793159450527210), (-3206792916888624962)⟩, true⟩

def words05 : List Nat := [360571592756717235, 360571624350796872, 360571713374299346, 360571779250383698, 360571796125081978, 360571812991665178, 360571887229476732, 360572015287441402, 360572200635803397, 360572385895087416]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 4150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 4100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360714410158004158, 360714410244288430⟩, ⟨(-590211593928126248), (-590211349537819564)⟩, true⟩

def words06 : List Nat := [360572535385158965, 360572628477418841, 360572744003108544, 360572859473336903, 360572923241921038, 360572930706696930, 360572930706738484, 360572909390964340, 360572888085407649, 360572906684101948]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 4160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 4100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360185384371439650, 360185384458160295⟩, ⟨1619294742510036361, 1619294988722236673⟩, true⟩

def words07 : List Nat := [360572966160328446, 360573025608059112, 360573048356515763, 360573048356562008, 360573014947202889, 360572963856556403, 360572918595288402, 360572918595334660, 360572868303223884, 360572775603787625]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 4170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 4100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360862638746309584, 360862638833467785⟩, ⟨(-1214934201994828245), (-1214933953951485455)⟩, true⟩

def words08 : List Nat := [360572682948683992, 360572617393435450, 360572606064926875, 360572615112021780, 360572615112064963, 360572577002458386, 360572599765795143, 360572625820554938, 360572678462548344, 360572747649036508]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 4180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 4100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360262232067052750, 360262232154654541⟩, ⟨1304497342191315062, 1304497592095527280⟩, true⟩

def words09 : List Nat := [360572772900705325, 360572798140334261, 360572819719255657, 360572871238386549, 360572907259673853, 360572943263803407, 360572949852554156, 360572949852600697, 360572900788107673, 360572826819439191]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 4190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 4100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 4100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk041
