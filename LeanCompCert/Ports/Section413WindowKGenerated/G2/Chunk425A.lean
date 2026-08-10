import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk425A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360660180503642981, 360660191684655296⟩, ⟨(-3298584809823921384), (-3298263668641000018)⟩, true⟩

def state01 : KState := ⟨⟨360650039615877777, 360650050802402926⟩, ⟨(-2867777491394318240), (-2867456115889317626)⟩, true⟩

def words00 : List Nat := [360582588824273187, 360582589960823083, 360582591334339758, 360582592707976526, 360582593938676533, 360582594803920754, 360582595390731621, 360582595977573289, 360582597117526923, 360582598704924878]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 42500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 42500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591725580475254, 360591736772457888⟩, ⟨(-388549470931990789), (-388227863401461701)⟩, true⟩

def words01 : List Nat := [360582600276855834, 360582601848815614, 360582603059672947, 360582603983038892, 360582604545357298, 360582605107805149, 360582605586584071, 360582606080042016, 360582606295296765, 360582606510624877]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 42510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 42500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360631264421281554, 360631275618730054⟩, ⟨(-2069913668568078409), (-2069591828602395217)⟩, true⟩

def words02 : List Nat := [360582607122252033, 360582608082116024, 360582609200286022, 360582610318512120, 360582610913646837, 360582611428769762, 360582612055654828, 360582612682679257, 360582613689407176, 360582614834158744]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 42520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 42500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360601625202811598, 360601636405784078⟩, ⟨(-809058978755987029), (-808736903828489429)⟩, true⟩

def words03 : List Nat := [360582615700957638, 360582616567789643, 360582617987036818, 360582619795362924, 360582621381137096, 360582622966933797, 360582624131812368, 360582624747018930, 360582625194408234, 360582625641960273]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 42530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 42500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360607207506186570, 360607218714616630⟩, ⟨(-1046672630779133357), (-1046350323659184101)⟩, true⟩

def words04 : List Nat := [360582626326484642, 360582626626619074, 360582626627140593, 360582626562564693, 360582626497897463, 360582626327249827, 360582626879197246, 360582627431233524, 360582627637078119, 360582628215599940]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 42540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 42500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk425A
