import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk435A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk435B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk435A

def state06 : KState := ⟨⟨360573488144117935, 360573499913659486⟩, ⟨421898735893204747, 422245202839258173⟩, true⟩

def words05 : List Nat := [360583195817345518, 360583195153034194, 360583194488639728, 360583194401211734, 360583194401709736, 360583194390607001, 360583194379439918, 360583194102811354, 360583193551549341, 360583193329702628]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 43550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 43500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360555810737937535, 360555822513081130⟩, ⟨1191937931228214778, 1192284642227978626⟩, true⟩

def words06 : List Nat := [360583193107666840, 360583192823598418, 360583192303026049, 360583191455514828, 360583190607945602, 360583189625545565, 360583188958717209, 360583188519777340, 360583188080787586, 360583187320109544]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 43560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 43500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360584891490790337, 360584903271546015⟩, ⟨(-75438645056390152), (-75091689510258578)⟩, true⟩

def words07 : List Nat := [360583186692544099, 360583185882891373, 360583185073101667, 360583184789707433, 360583183981540642, 360583182692488819, 360583181403379564, 360583180640682419, 360583180194071518, 360583180234224470]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 43570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 43500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584092476498375, 360584104262927433⟩, ⟨(-40633622181971643), (-40286419362129829)⟩, true⟩

def words08 : List Nat := [360583180234754465, 360583180034873234, 360583180380141817, 360583180725568595, 360583180785219318, 360583180909060139, 360583180909595548, 360583180695105214, 360583180480519929, 360583180071709931]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 43580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 43500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360557048648665799, 360557060440694334⟩, ⟨1138452580987340835, 1138800027916905315⟩, true⟩

def words09 : List Nat := [360583180619307477, 360583181166993807, 360583181317755167, 360583181318350359, 360583181118317052, 360583180783462412, 360583180638725925, 360583180639321084, 360583180305852441, 360583179707389676]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 43590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 43500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 43500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk435B
