import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk550A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk550B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk550A

def state06 : KState := ⟨⟨360572766098410091, 360572785266575237⟩, ⟨493790638556672245, 494503714514634475⟩, true⟩

def words05 : List Nat := [360581764456337674, 360581765282098010, 360581765940523389, 360581766270185365, 360581766271990223, 360581766273980255, 360581766604917981, 360581766607198059, 360581766607879947, 360581766445552982]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 55050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 55000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360602562636665976, 360602581812070441⟩, ⟨(-1146885881891327876), (-1146172407301913720)⟩, true⟩

def words06 : List Nat := [360581766449079699, 360581766891196161, 360581767296478799, 360581767701891347, 360581767825992457, 360581767901250531, 360581768204242620, 360581768507452098, 360581768802247708, 360581769180970554]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 55060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 55000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602243985635221, 360602263168333347⟩, ⟨(-1129325517434198422), (-1128611641147347780)⟩, true⟩

def words07 : List Nat := [360581769351732766, 360581769522565361, 360581770022238380, 360581770729928069, 360581771350510188, 360581771971207459, 360581772343539118, 360581772387383125, 360581772760020669, 360581773132910110]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 55070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 55000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579118311076735, 360579137500996016⟩, ⟨144395232662145167, 145109506726710305⟩, true⟩

def words08 : List Nat := [360581773444264173, 360581773445029888, 360581773427914472, 360581773128027671, 360581772828027555, 360581772352485971, 360581772042235720, 360581771931943824, 360581771821573623, 360581771545409280]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 55080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 55000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588511878160251, 360588531075307864⟩, ⟨(-373094720674358853), (-372380048364890215)⟩, true⟩

def words09 : List Nat := [360581771698269226, 360581771899159128, 360581772288755581, 360581772616718792, 360581772663924271, 360581772711187869, 360581772711819682, 360581772692640482, 360581772815920693, 360581772939369045]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 55090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 55000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 55000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk550B
