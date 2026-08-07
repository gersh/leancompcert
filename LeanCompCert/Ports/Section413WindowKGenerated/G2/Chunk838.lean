import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk838

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360567655836775718, 360567701742197613⟩, ⟨1234389666288925091, 1236987612389485445⟩, true⟩

def state01 : KState := ⟨⟨360581884631441603, 360581930548211519⟩, ⟨41980787425917521, 44579684546475139⟩, true⟩

def words00 : List Nat := [360582462755716203, 360582462678755581, 360582462785928720, 360582462900393627, 360582462901503285, 360582462880010338, 360582462716187224, 360582462643237182, 360582462569930726, 360582462461879894]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590442111792716, 360590488040029684⟩, ⟨(-675295597168847522), (-672695738938319220)⟩, true⟩

def words01 : List Nat := [360582462456628724, 360582462334507528, 360582462231069231, 360582462340077132, 360582462412978864, 360582462486075138, 360582462487157027, 360582462473373360, 360582462558584526, 360582462655711455]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583265841661936, 360583311781216782⟩, ⟨(-73770186045883435), (-71169379093219401)⟩, true⟩

def words02 : List Nat := [360582462868521552, 360582462939504845, 360582462940576529, 360582462940333569, 360582462939906463, 360582462842058345, 360582462835730504, 360582462857186295, 360582462858258028, 360582462818671981]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360581975660930220, 360582021611853448⟩, ⟨34406569543456402, 37008329562686600⟩, true⟩

def words03 : List Nat := [360582462851860880, 360582462885418763, 360582463060746107, 360582463127173412, 360582463128296054, 360582463061986143, 360582462995451947, 360582463031026826, 360582463032017657, 360582463027998042]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360600756592906166, 360600802555291154⟩, ⟨(-1540350510405154852), (-1537747789378804986)⟩, true⟩

def words04 : List Nat := [360582463023804927, 360582462948576293, 360582463011982254, 360582463115594157, 360582463151016787, 360582463220643390, 360582463221717599, 360582463204093044, 360582463283911363, 360582463504005197]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360581638825794731, 360581684799518469⟩, ⟨62785654094612770, 65389325933051028⟩, true⟩

def words05 : List Nat := [360582463825902510, 360582464148022660, 360582464337586663, 360582464385274857, 360582464386282567, 360582464373175252, 360582464487349683, 360582464550406861, 360582464551478899, 360582464543448031]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 83850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 83800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594603545631359, 360594649530711116⟩, ⟨(-1024517486942681976), (-1021912862730666518)⟩, true⟩

def words06 : List Nat := [360582464573652584, 360582464685206182, 360582464838873848, 360582464992772009, 360582465025492499, 360582465026698544, 360582464998176503, 360582464966405393, 360582465043204024, 360582465189726382]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 83860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 83800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597315036893216, 360597361033444168⟩, ⟨(-1251937918076065008), (-1249332331718656568)⟩, true⟩

def words07 : List Nat := [360582465264709954, 360582465339813017, 360582465556694021, 360582465884690030, 360582466107762215, 360582466331022992, 360582466475530320, 360582466572022197, 360582466750564297, 360582466929514570]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 83870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 83800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584275645739791, 360584321653641653⟩, ⟨(-158205754650532046), (-155599216123121048)⟩, true⟩

def words08 : List Nat := [360582467060528993, 360582467061732651, 360582467050967242, 360582466969211783, 360582466887263882, 360582466738296098, 360582466785456541, 360582466864976284, 360582466866064937, 360582466875225338]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 83880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 83800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593087976983086, 360593133996241127⟩, ⟨(-897517127267503955), (-894909636014362337)⟩, true⟩

def words09 : List Nat := [360582467040259153, 360582467205642606, 360582467461143183, 360582467575054253, 360582467576187312, 360582467545838088, 360582467515266356, 360582467482666500, 360582467610773716, 360582467739152245]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 83890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 83800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 83800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk838
