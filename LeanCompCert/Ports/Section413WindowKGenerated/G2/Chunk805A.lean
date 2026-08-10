import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk805A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk805A
