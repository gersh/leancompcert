import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk438A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571396374723636, 360571408279693595⟩, ⟨515536052810476365, 515888435285448941⟩, true⟩

def state01 : KState := ⟨⟨360604411818360769, 360604423728961911⟩, ⟨(-930701550637326335), (-930348921488700893)⟩, true⟩

def words00 : List Nat := [360583186538054091, 360583186739994754, 360583186740532890, 360583186632430393, 360583186524235165, 360583186461892828, 360583187006978276, 360583187552153566, 360583187733784176, 360583188219124457]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 43800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 43800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360618302853221779, 360618314769474730⟩, ⟨(-1539419931978907540), (-1539067055196705770)⟩, true⟩

def words01 : List Nat := [360583189103186068, 360583189987388641, 360583190592192251, 360583190975124090, 360583190975676510, 360583190862622267, 360583190962779904, 360583191487245059, 360583192289264749, 360583193091393520]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 43810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 43800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592103401295151, 360592115323249841⟩, ⟨(-391440515757482601), (-391087389096755101)⟩, true⟩

def words02 : List Nat := [360583193617842240, 360583193625089623, 360583193782547592, 360583193940175829, 360583193966033811, 360583193966633825, 360583193824223290, 360583193280356836, 360583192736400904, 360583192702522576]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 43820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 43800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579584177219075, 360579596104808626⟩, ⟨157427255132048397, 157780628797256195⟩, true⟩

def words03 : List Nat := [360583193257984309, 360583193813535137, 360583194053110265, 360583194463589287, 360583194532411769, 360583194601389248, 360583195015068419, 360583195196440184, 360583195196978472, 360583195115501995]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 43830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 43800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602999577472629, 360603011510723362⟩, ⟨(-869262549634580192), (-868908927755402844)⟩, true⟩

def words04 : List Nat := [360583195033902118, 360583195104366532, 360583195442099674, 360583195779930787, 360583195780483226, 360583195622945842, 360583195554458465, 360583195715627642, 360583196027143779, 360583196479646411]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 43840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 43800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk438A
