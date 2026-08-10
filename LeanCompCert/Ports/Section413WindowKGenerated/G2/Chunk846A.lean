import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk846A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585072418673343, 360585119239243852⟩, ⟨(-228452154826838604), (-225777152629589088)⟩, true⟩

def state01 : KState := ⟨⟨360579153180457939, 360579200012485117⟩, ⟨272358224008269781, 275034195497557863⟩, true⟩

def words00 : List Nat := [360582450564361780, 360582450622635820, 360582450623718272, 360582450611984835, 360582450600047760, 360582450592534355, 360582450643760613, 360582450695216091, 360582450696330991, 360582450623470788]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 84600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 84600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360588207077598527, 360588253921093029⟩, ⟨(-493733702366195513), (-491056760568879757)⟩, true⟩

def words01 : List Nat := [360582450663780120, 360582450742871779, 360582450936611604, 360582450991066701, 360582450992187457, 360582450927562189, 360582450862690624, 360582450781063283, 360582450838287273, 360582450908122622]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 84610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 84600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582885866256090, 360582932721345572⟩, ⟨(-43576616183400183), (-40898693165375223)⟩, true⟩

def words02 : List Nat := [360582450909205537, 360582450893778898, 360582450804360053, 360582450634066084, 360582450463454113, 360582450257502030, 360582450074743102, 360582449822204033, 360582449569438087, 360582449462336871]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 84620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 84600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567055516093912, 360567102382615771⟩, ⟨1296313105920656861, 1298991996519460595⟩, true⟩

def words03 : List Nat := [360582449608538727, 360582449754970313, 360582449831302886, 360582449886684052, 360582449906706750, 360582449927063917, 360582449928063697, 360582449924675555, 360582449821619737, 360582449641553856]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 84630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 84600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360578976115012929, 360579022993008137⟩, ⟨287272434972146757, 289952296731649967⟩, true⟩

def words04 : List Nat := [360582449461214895, 360582449378215637, 360582449364873953, 360582449325158776, 360582449285350645, 360582449114637169, 360582448804295702, 360582448590090154, 360582448375532649, 360582448300707271]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 84640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 84600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk846A
