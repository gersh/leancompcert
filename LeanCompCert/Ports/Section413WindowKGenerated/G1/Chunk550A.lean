import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk550A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362459451612604065, 362459495659219944⟩, ⟨1396138910642510108, 1397775452359787194⟩, true⟩

def state01 : KState := ⟨⟨362486821945380096, 362486866008540705⟩, ⟨(-109325172669245426), (-107687720906749020)⟩, true⟩

def words00 : List Nat := [371284909297542329, 371284909167759258, 371284908886757373, 371284908825956753, 371284908764602996, 371284908680702998, 371284908321601580, 371284908240112203, 371284908403992003, 371284908441492174]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 55000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 55000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362474923457588700, 362474967537601378⟩, ⟨545272462835294257, 546910841715151985⟩, true⟩

def words01 : List Nat := [371284908442884580, 371284908418766224, 371284908440444247, 371284908442483150, 371284908353619632, 371284908361089739, 371284908367099443, 371284908368949539, 371284907934821598, 371284907756462068]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 55010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 55000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362470480764970450, 362470524861462248⟩, ⟨789820000110311243, 791459285756797357⟩, true⟩

def words02 : List Nat := [371284907726372172, 371284907728236226, 371284907643979032, 371284907560880224, 371284907477050512, 371284907469675535, 371284907298264670, 371284907266495964, 371284907234131522, 371284907185390230]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 55020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 55000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498069340722498, 362498113453943640⟩, ⟨(-728502325808347803), (-726862119460352941)⟩, true⟩

def words03 : List Nat := [371284906972299895, 371284907021531874, 371284907239056065, 371284907240939002, 371284907184417246, 371284907076230406, 371284907135355565, 371284907140154847, 371284907381352642, 371284907623390773]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 55030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 55000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362492931572438635, 362492975702388332⟩, ⟨(-445748139203064041), (-444107012031111291)⟩, true⟩

def words04 : List Nat := [371284907798098380, 371284907799960086, 371284907939232198, 371284908133041379, 371284908396688919, 371284908398545180, 371284908325919737, 371284908228783799, 371284908361273216, 371284908509929865]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 55040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 55000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk550A
