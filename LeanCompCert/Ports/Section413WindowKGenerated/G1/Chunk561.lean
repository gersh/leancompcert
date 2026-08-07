import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk561

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486769640949101, 362486815539887855⟩, ⟨(-107893835366519020), (-106154393334477496)⟩, true⟩

def state01 : KState := ⟨⟨362474729801734520, 362474775717469251⟩, ⟨567634660298404969, 569375044672806181⟩, true⟩

def words00 : List Nat := [371284923690959109, 371284923692847768, 371284923622205130, 371284923552167175, 371284923481416133, 371284923413493140, 371284923196464481, 371284923206906244, 371284923208318796, 371284923196433301]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 56100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 56100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486042663036759, 362486088595881026⟩, ⟨(-67168618904211674), (-65427274429704408)⟩, true⟩

def words01 : List Nat := [371284923016877146, 371284923001311798, 371284923284164057, 371284923286053020, 371284923163889230, 371284922989130925, 371284922834486460, 371284922836568702, 371284922747793983, 371284922770709884]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 56110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 56100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486965551685217, 362487011501576849⟩, ⟨(-118986491596715589), (-117244190335607827)⟩, true⟩

def words02 : List Nat := [371284922786220421, 371284922788122422, 371284922566459963, 371284922615865401, 371284922761549554, 371284922763475951, 371284922710762573, 371284922647625113, 371284922702159570, 371284922741527401]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 56120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 56100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483032447866569, 362483078414771432⟩, ⟨101883522415987989, 103626778717387153⟩, true⟩

def words03 : List Nat := [371284923097167586, 371284923453545893, 371284923701646509, 371284923731933842, 371284923839160112, 371284923947332425, 371284924338554377, 371284924340444258, 371284924309043114, 371284924278303983]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 56130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 56100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490538104346473, 362490584088162340⟩, ⟨(-319466169800499353), (-317721964028620073)⟩, true⟩

def words04 : List Nat := [371284924479974800, 371284924557089146, 371284924861884352, 371284925167475512, 371284925452018284, 371284925453908761, 371284925363471248, 371284925349828956, 371284925636265313, 371284925738996188]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 56140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 56100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362493253072019207, 362493299073099010⟩, ⟨(-471910696061808891), (-470165520838804741)⟩, true⟩

def words05 : List Nat := [371284925796546926, 371284925854732595, 371284926196160567, 371284926426267575, 371284926668421967, 371284926911265022, 371284927153510872, 371284927155402105, 371284927177517034, 371284927328991199]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 56150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 56100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481322622491332, 362481368640429268⟩, ⟨198129456129615237, 199875578190875221⟩, true⟩

def words06 : List Nat := [371284927585794695, 371284927587685319, 371284927422228779, 371284927234768717, 371284927046605383, 371284926928375247, 371284926825646869, 371284926934119361, 371284927042925125, 371284927044883441]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 56160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 56100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496272999075486, 362496319034076077⟩, ⟨(-641709778903998046), (-639962698345028890)⟩, true⟩

def words07 : List Nat := [371284927236165983, 371284927491749343, 371284927875129820, 371284927877021202, 371284927838376332, 371284927722114906, 371284927649194807, 371284927651298322, 371284927741503974, 371284927946371248]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 56170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 56100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477821999447461, 362477868051529254⟩, ⟨394959773117642259, 396707813388183937⟩, true⟩

def words08 : List Nat := [371284928130019655, 371284928131944074, 371284928206677050, 371284928363129268, 371284928552091980, 371284928553992627, 371284928440249267, 371284928324496581, 371284928208007066, 371284928165666791]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 56180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 56100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362466850020609832, 362466896089745445⟩, ⟨1011618834895859416, 1013367833506727558⟩, true⟩

def words09 : List Nat := [371284928206723190, 371284928374214369, 371284928541022122, 371284928542914093, 371284928287720213, 371284928129760474, 371284928126942032, 371284928128834065, 371284927864563270, 371284927545857665]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 56190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 56100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 56100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk561
