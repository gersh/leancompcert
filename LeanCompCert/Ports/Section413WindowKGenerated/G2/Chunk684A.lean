import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk684A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592587180382266, 360592617278843213⟩, ⟨(-669864896421427630), (-668474263657846346)⟩, true⟩

def state01 : KState := ⟨⟨360597469264939198, 360597499372504747⟩, ⟨(-1003821332476561309), (-1002430076912253759)⟩, true⟩

def words00 : List Nat := [360582844708071995, 360582844912978843, 360582845002222559, 360582845091586268, 360582845126863043, 360582845297456639, 360582845619846129, 360582845942413952, 360582846103313168, 360582846318508866]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 68400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 68400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591761618420134, 360591791735130300⟩, ⟨(-613398730857899936), (-612006849666071172)⟩, true⟩

def words01 : List Nat := [360582846459139386, 360582846600035237, 360582846804467941, 360582846855056712, 360582846855948653, 360582846724722648, 360582846593315851, 360582846749490199, 360582846881014058, 360582847012754625]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 68410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 68400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360564413453343623, 360564443579249593⟩, ⟨1257777875207374777, 1259170385622935655⟩, true⟩

def words02 : List Nat := [360582847037568916, 360582847038536263, 360582846849966733, 360582846809199725, 360582846768196117, 360582846510183578, 360582846038789977, 360582845460511127, 360582844882064279, 360582844432466354]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 68420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 68400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360537998500353247, 360538028635382301⟩, ⟨3065499575818041854, 3066892710572730244⟩, true⟩

def words03 : List Nat := [360582844164357332, 360582843929451908, 360582843694426033, 360582843352791925, 360582842797748483, 360582842189136414, 360582841580248413, 360582841184659301, 360582840696370273, 360582840042608671]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 68430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 68400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360601449711302350, 360601479855466985⟩, ⟨(-1277424470243229629), (-1276030710206842359)⟩, true⟩

def words04 : List Nat := [360582839388645936, 360582838896725864, 360582838610112771, 360582838536754077, 360582838463335613, 360582838207381129, 360582837958054599, 360582837922063438, 360582838061765257, 360582838335106336]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 68440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 68400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk684A
