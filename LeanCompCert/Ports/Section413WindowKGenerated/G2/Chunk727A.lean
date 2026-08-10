import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk727A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578048604438562, 360578082771274004⟩, ⟨311245423660089000, 312923175918544570⟩, true⟩

def state01 : KState := ⟨⟨360588411015369555, 360588445191969546⟩, ⟨(-442084831503175844), (-440406369314862464)⟩, true⟩

def words00 : List Nat := [360582387150334265, 360582387430269332, 360582387711479052, 360582387992876856, 360582388092349212, 360582388093381889, 360582388102459924, 360582388202131359, 360582388202987654, 360582388249150511]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 72700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 72700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582220573358232, 360582254759790474⟩, ⟨8021476474908220, 9700653615414994⟩, true⟩

def words01 : List Nat := [360582388250080347, 360582388239373765, 360582388228471829, 360582388313250390, 360582388355606721, 360582388398148778, 360582388399069226, 360582388347528934, 360582388157762636, 360582388157117419]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 72710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 72700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592918645356357, 360592952841531874⟩, ⟨(-770081776482586809), (-768401890762584099)⟩, true⟩

def words02 : List Nat := [360582388175866101, 360582388176903930, 360582388141424635, 360582387958622664, 360582387775658425, 360582387545789640, 360582387581122606, 360582387693766944, 360582387710638337, 360582387856989347]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 72720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 72700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360618765633886799, 360618799839812024⟩, ⟨(-2650073213349166864), (-2648392618485963326)⟩, true⟩

def words03 : List Nat := [360582388161170413, 360582388465657346, 360582388958519582, 360582389341475936, 360582389561419540, 360582389781432817, 360582389997401249, 360582390310439210, 360582390811818061, 360582391313417200]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 72730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 72700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592813436948589, 360592847652713173⟩, ⟨(-762298717342206885), (-760617406715219209)⟩, true⟩

def words04 : List Nat := [360582391720847096, 360582392021724313, 360582392260415662, 360582392499415483, 360582392690255427, 360582392692685532, 360582392693615169, 360582392576795901, 360582392459778382, 360582392574340158]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 72740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 72700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk727A
