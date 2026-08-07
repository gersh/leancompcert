import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk743

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360604384718853280, 360604420467747727⟩, ⟨(-1643660277241030642), (-1641866238912192880)⟩, true⟩

def state01 : KState := ⟨⟨360583726981590867, 360583762740547965⟩, ⟨(-108774751127619329), (-106979965094050285)⟩, true⟩

def words00 : List Nat := [360582323177018895, 360582323258538976, 360582323470489023, 360582323682755866, 360582323728392804, 360582323729449957, 360582323652649549, 360582323440625587, 360582323228401771, 360582323115659402]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 74300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 74300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360562780602584847, 360562816371503260⟩, ⟨1447936250411176478, 1449731776720713412⟩, true⟩

def words01 : List Nat := [360582323316681980, 360582323517920013, 360582323601763457, 360582323602820635, 360582323554689700, 360582323433475916, 360582323370342249, 360582323371399355, 360582323249897654, 360582322988520493]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 74310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 74300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587240088950894, 360587275867848858⟩, ⟨(-370008256918417464), (-368211988878643908)⟩, true⟩

def words02 : List Nat := [360582322726914887, 360582322519482646, 360582322464438429, 360582322527923559, 360582322528899817, 360582322437071953, 360582322350286274, 360582322225281282, 360582322120099268, 360582322187838114]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 74320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 74300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583095033315358, 360583130822309154⟩, ⟨(-61947426932816496), (-60150408422486534)⟩, true⟩

def words03 : List Nat := [360582322188789893, 360582322166433487, 360582322143891237, 360582322037487652, 360582322038372561, 360582321997936393, 360582321957384693, 360582321807783536, 360582321695318109, 360582321707440879]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 74330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 74300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360554847060160517, 360554882859106629⟩, ⟨2038147147317861729, 2039944905734800351⟩, true⟩

def words04 : List Nat := [360582321780921494, 360582321781978935, 360582321674797439, 360582321477323802, 360582321279683081, 360582321036746480, 360582320884744432, 360582320606272330, 360582320327707751, 360582319912310864]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 74340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 74300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk743
