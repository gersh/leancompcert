import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk316A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk316B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk316A

def state06 : KState := ⟨⟨360518328828152784, 360518334884618612⟩, ⟨2031434911683986800, 2031564576046572522⟩, true⟩

def words05 : List Nat := [360582520192074614, 360582518338149683, 360582516484299271, 360582514124455113, 360582512390971024, 360582510101137027, 360582507811324583, 360582506515659237, 360582505090950038, 360582503064531644]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 31650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 31600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360562832375549217, 360562838435996488⟩, ⟨622232242027569732, 622362032462343078⟩, true⟩

def words06 : List Nat := [360582501038152042, 360582498987349959, 360582497432213750, 360582496870852913, 360582496309494670, 360582494895474566, 360582492863867872, 360582491825971192, 360582490788008623, 360582489905288005]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 31660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 31600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360533328665244004, 360533334729706092⟩, ⟨1556703479871122682, 1556833397475003388⟩, true⟩

def words07 : List Nat := [360582489285181032, 360582487869878796, 360582486454585927, 360582485477340750, 360582485005834436, 360582483843584312, 360582482681361652, 360582481021975693, 360582478748836138, 360582477198060733]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 31670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 31600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360556969803901728, 360556975872335644⟩, ⟨807639399215224302, 807769442667024816⟩, true⟩

def words08 : List Nat := [360582475647237981, 360582474391634514, 360582473454737079, 360582471905938974, 360582470357169924, 360582468559213278, 360582467266255565, 360582466965427308, 360582466664580937, 360582465599147479]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 31680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 31600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360613231197909429, 360613237270324437⟩, ⟨(-975762784910321996), (-975632615278439270)⟩, true⟩

def words09 : List Nat := [360582464795170296, 360582463737240310, 360582462679252987, 360582462197839606, 360582461969412970, 360582460890279400, 360582459811126397, 360582459264857481, 360582460215777771, 360582461187069069]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 31690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 31600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 31600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk316B
