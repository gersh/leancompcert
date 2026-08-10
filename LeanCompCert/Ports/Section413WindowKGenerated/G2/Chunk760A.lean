import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk760A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360563502388970111, 360563539859357069⟩, ⟨1415322361272858651, 1417245775585106177⟩, true⟩

def state01 : KState := ⟨⟨360608890879465650, 360608928360068044⟩, ⟨(-2034410262281674626), (-2032486071545172292)⟩, true⟩

def words00 : List Nat := [360582187585599256, 360582187543938401, 360582187747312596, 360582187950888770, 360582188003584538, 360582188104244320, 360582188251506115, 360582188399079365, 360582188639540067, 360582188992456183]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 76000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 76000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590847623823063, 360590885114749058⟩, ⟨(-662856920087734289), (-660931944604224253)⟩, true⟩

def words01 : List Nat := [360582189234853801, 360582189477359346, 360582189715529325, 360582190068960644, 360582190332709862, 360582190596627409, 360582190773796415, 360582190813233946, 360582190928480214, 360582191044102734]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 76010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 76000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360572800297261300, 360572837798380506⟩, ⟨709149593275749292, 711075343700063342⟩, true⟩

def words02 : List Nat := [360582191186235274, 360582191187318469, 360582191156786407, 360582191039228585, 360582190921489873, 360582190759964277, 360582190684839102, 360582190605812447, 360582190526669758, 360582190361101802]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 76020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 76000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360611415305962245, 360611452817309713⟩, ⟨(-2226960780518383656), (-2225034252388504088)⟩, true⟩

def words03 : List Nat := [360582190288746314, 360582190339737538, 360582190527768428, 360582190720966127, 360582190747255551, 360582190773627896, 360582190851448182, 360582191064731623, 360582191450428158, 360582191836360114]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 76030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 76000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587666327139057, 360587703848831677⟩, ⟨(-421133152937620104), (-419205838114629980)⟩, true⟩

def words04 : List Nat := [360582192061406709, 360582192148697061, 360582192206434893, 360582192264482562, 360582192265389662, 360582192248735511, 360582192117891747, 360582191900656494, 360582191683200289, 360582191681495092]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 76040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 76000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk760A
