import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk935A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk935B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk935A

def state06 : KState := ⟨⟨360600776001750439, 360600833713967294⟩, ⟨(-1759989973162438570), (-1756343858749579178)⟩, true⟩

def words05 : List Nat := [360582061130917029, 360582061107204500, 360582061172102194, 360582061200468544, 360582061201761151, 360582061111321380, 360582061043032068, 360582061130973401, 360582061332715491, 360582061534760685]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360607841092459560, 360607898817591506⟩, ⟨(-2421062298363510632), (-2417414975550255720)⟩, true⟩

def words06 : List Nat := [360582061665087600, 360582061837490082, 360582062123800978, 360582062410519929, 360582062668045615, 360582062907943992, 360582063090291780, 360582063272787804, 360582063452408947, 360582063730058507]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591496262299923, 360591554000183283⟩, ⟨(-891527768293233481), (-887879252266530021)⟩, true⟩

def words07 : List Nat := [360582064099920086, 360582064470033539, 360582064766166421, 360582065073586763, 360582065325497783, 360582065577784973, 360582065819298294, 360582065979405047, 360582066082001043, 360582066184790559]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360598590907812595, 360598648658504406⟩, ⟨(-1555482893601551818), (-1551833178897707254)⟩, true⟩

def words08 : List Nat := [360582066401416844, 360582066675446398, 360582066913175806, 360582067151139790, 360582067277407746, 360582067320246177, 360582067347298958, 360582067374752486, 360582067471278321, 360582067649872191]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589233422019073, 360589291185619382⟩, ⟨(-679624261942151255), (-675973339067355883)⟩, true⟩

def words09 : List Nat := [360582067771473879, 360582067893209565, 360582068107832090, 360582068393835516, 360582068650710960, 360582068907802073, 360582069076956084, 360582069168405592, 360582069246666680, 360582069325392811]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk935B
