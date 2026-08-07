import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk438

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

def state06 : KState := ⟨⟨360583493216388748, 360583505155336926⟩, ⟨(-13767584467339129), (-13413712726939541)⟩, true⟩

def words05 : List Nat := [360583196629333779, 360583196779080781, 360583197448171427, 360583198378708139, 360583198941022524, 360583199503400104, 360583199669304768, 360583199669903706, 360583199324448548, 360583199332106108]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 43850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 43800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360611663445628183, 360611675390224928⟩, ⟨(-1249449617442886754), (-1249095497927650116)⟩, true⟩

def words06 : List Nat := [360583199580378069, 360583200058638919, 360583200275405146, 360583200492226866, 360583200500929325, 360583200769569584, 360583201557129860, 360583202344772870, 360583202731799060, 360583203381428055]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 43860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 43800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360610061559966997, 360610073510218578⟩, ⟨(-1179167273207493197), (-1178812905586551181)⟩, true⟩

def words07 : List Nat := [360583204256019705, 360583205130745965, 360583206378477996, 360583207108254225, 360583207393546777, 360583207678874455, 360583207892615525, 360583208427737033, 360583209040464660, 360583209653296755]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 43870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 43800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586389652227645, 360586401608196434⟩, ⟨(-140564688552695539), (-140210070033947419)⟩, true⟩

def words08 : List Nat := [360583210004846135, 360583210077811440, 360583210137144360, 360583210196648955, 360583210197150707, 360583210030652773, 360583209346330766, 360583208401083151, 360583207455761122, 360583207102032666]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 43880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 43800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360557230707064552, 360557242668668779⟩, ⟨1139519985573239501, 1139874851460588065⟩, true⟩

def words09 : List Nat := [360583207693824532, 360583208285704238, 360583208615196970, 360583208776249492, 360583208804438225, 360583208832784994, 360583208847588745, 360583208848188512, 360583208518100138, 360583207927244192]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 43890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 43800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 43800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk438
