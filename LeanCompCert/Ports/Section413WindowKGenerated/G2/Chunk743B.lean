import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk743A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk743B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk743A

def state06 : KState := ⟨⟨360594118106091536, 360594153915024337⟩, ⟨(-881838089766878344), (-880039588792522050)⟩, true⟩

def words05 : List Nat := [360582319544145332, 360582319319201234, 360582319093952808, 360582319049513580, 360582319046290546, 360582318888898999, 360582318753436796, 360582318901981426, 360582319061996503, 360582319222258069]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 74350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 74300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589328511734503, 360589364330741991⟩, ⟨(-525797099564367052), (-523997849385972300)⟩, true⟩

def words06 : List Nat := [360582319242565252, 360582319243623045, 360582319102414428, 360582319122826653, 360582319123712106, 360582319076003401, 360582318974707509, 360582318782352827, 360582318589782918, 360582318602576632]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 74360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 74300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360556403208449221, 360556439037414002⟩, ⟨1923045519114360133, 1924845509867612205⟩, true⟩

def words07 : List Nat := [360582318726211548, 360582318850039978, 360582318859404839, 360582318860463281, 360582318765852372, 360582318509517187, 360582318252867509, 360582318176916115, 360582317920276192, 360582317573443414]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 74370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 74300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596570383945722, 360596606222915403⟩, ⟨(-1064716731960606681), (-1062915996995856681)⟩, true⟩

def words08 : List Nat := [360582317226380199, 360582317063356494, 360582317247896303, 360582317432633789, 360582317468286486, 360582317469349572, 360582317566785164, 360582317683547576, 360582317795996361, 360582317989164065]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 74380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 74300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360573195972934496, 360573231821979373⟩, ⟨674261618221627009, 676063102731001713⟩, true⟩

def words09 : List Nat := [360582318082524570, 360582318176000735, 360582318297340914, 360582318509027347, 360582318674871127, 360582318840901467, 360582318916491148, 360582318917549397, 360582318812567264, 360582318691639736]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 74390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 74300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 74300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk743B
