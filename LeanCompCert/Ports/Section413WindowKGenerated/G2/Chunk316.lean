import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk316

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360493006095528375, 360493012128105678⟩, ⟨2832274615808604946, 2832403524578316022⟩, true⟩

def state01 : KState := ⟨⟨360533493088766276, 360533499125311105⟩, ⟨1552639142680014755, 1552768176842993439⟩, true⟩

def words00 : List Nat := [360582642314977192, 360582640476803837, 360582639304220056, 360582637532814560, 360582635761495191, 360582633029620844, 360582629297804357, 360582626563617602, 360582623829476725, 360582621813600982]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 31600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 31600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360502838024074969, 360502844064630843⟩, ⟨2521916162732582772, 2522045323704402762⟩, true⟩

def words01 : List Nat := [360582620260001300, 360582618061288160, 360582615862626557, 360582614377571406, 360582613638776172, 360582612649109385, 360582611659460235, 360582610162464618, 360582607665898997, 360582605143811881]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 31610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 31600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360506671698037149, 360506677742554085⟩, ⟨2400624463599870023, 2400753749840324765⟩, true⟩

def words02 : List Nat := [360582602621743681, 360582600824432295, 360582598406850021, 360582595420049166, 360582592433371717, 360582588622130162, 360582585606701459, 360582583587410179, 360582581568202441, 360582578904420678]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 31620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 31600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360510104282698213, 360510110331191156⟩, ⟨2291950102130163694, 2292079514151514166⟩, true⟩

def words03 : List Nat := [360582576505179699, 360582574779225089, 360582573053262441, 360582571302108566, 360582568552561026, 360582564893754629, 360582561235097232, 360582557905327710, 360582555082925869, 360582552793711748]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 31630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 31600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360505057946447196, 360505063998947484⟩, ⟨2451436419043152601, 2451565957876524163⟩, true⟩

def words04 : List Nat := [360582550504574450, 360582547662875014, 360582544546434032, 360582542425093064, 360582540303770240, 360582537932528501, 360582534563766254, 360582530257124853, 360582525950674399, 360582522639006774]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 31640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 31600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk316
