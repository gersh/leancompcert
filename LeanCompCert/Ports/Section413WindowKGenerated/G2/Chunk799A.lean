import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk799A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360562511053647658, 360562552631373718⟩, ⟨1565417477535253338, 1567661129993167464⟩, true⟩

def state01 : KState := ⟨⟨360596689017671597, 360596730606174169⟩, ⟨(-1165544174455302549), (-1163299660900314969)⟩, true⟩

def words00 : List Nat := [360582172676226808, 360582172600114023, 360582172769199412, 360582172938507087, 360582172959895776, 360582172961038462, 360582172846436516, 360582172868139874, 360582172981903762, 360582173165259898]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 79900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 79900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360581117601068308, 360581159200481406⟩, ⟨78885559791839977, 81130945260126229⟩, true⟩

def words01 : List Nat := [360582173250889725, 360582173336647308, 360582173548560361, 360582173856390912, 360582174060725784, 360582174265235405, 360582174360487266, 360582174362893088, 360582174363833549, 360582174352449126]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 79910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 79900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586575106207216, 360586616716383666⟩, ⟨(-357326760429175647), (-355080514701127495)⟩, true⟩

def words02 : List Nat := [360582174453070034, 360582174454213052, 360582174451817226, 360582174371190545, 360582174290375396, 360582174121491688, 360582174200535790, 360582174304688193, 360582174321672341, 360582174378433420]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 79920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 79900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360589295231427629, 360589336852409236⟩, ⟨(-574795285654303685), (-572548176216412413)⟩, true⟩

def words03 : List Nat := [360582174546435411, 360582174714768614, 360582174828060514, 360582174889319811, 360582174890374348, 360582174819159453, 360582174747738534, 360582174603497049, 360582174627334726, 360582174718132502]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 79930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 79900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577813461796331, 360577855093661820⟩, ⟨343017708992221990, 345265688538558930⟩, true⟩

def words04 : List Nat := [360582174730436659, 360582174731579807, 360582174599077747, 360582174611757138, 360582174612714148, 360582174554360030, 360582174388223173, 360582174098730039, 360582173809016461, 360582173613843666]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 79940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 79900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk799A
