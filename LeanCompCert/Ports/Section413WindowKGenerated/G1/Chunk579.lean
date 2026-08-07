import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk579

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362475357136850290, 362475406151408827⟩, ⟨552556986569815468, 554474035289900802⟩, true⟩

def state01 : KState := ⟨⟨362478689505241809, 362478738537218340⟩, ⟨359664164305887155, 361582221616044201⟩, true⟩

def words00 : List Nat := [371284982528773293, 371284982530742384, 371284982458889762, 371284982386300835, 371284982312889443, 371284982293678043, 371284982219723680, 371284982317293464, 371284982400185945, 371284982402209120]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 57900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 57900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498051552343292, 362498100602037330⟩, ⟨(-761713984600394392), (-759794901183116254)⟩, true⟩

def words01 : List Nat := [371284982310303236, 371284982327226294, 371284982562538037, 371284982564495658, 371284982479961172, 371284982329193220, 371284982323233409, 371284982366103750, 371284982593922686, 371284982822627736]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 57910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 57900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487286092768900, 362487335160079564⟩, ⟨(-138183225975970788), (-136263122111325032)⟩, true⟩

def words02 : List Nat := [371284983044503339, 371284983046458283, 371284982992027514, 371284983115676448, 371284983245557569, 371284983247525760, 371284983111547791, 371284982974770870, 371284982954809900, 371284982997643022]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 57920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 57900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362463635624787246, 362463684709705414⟩, ⟨1232095086510970425, 1234016210467599223⟩, true⟩

def words03 : List Nat := [371284983258166189, 371284983519490971, 371284983743998699, 371284983745954217, 371284983612907761, 371284983570589161, 371284983564402145, 371284983566357996, 371284983249277980, 371284982883859153]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 57930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 57900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493335811667276, 362493384914088120⟩, ⟨(-488864405349078047), (-486942267198743237)⟩, true⟩

def words04 : List Nat := [371284982517608688, 371284982349120389, 371284982079437242, 371284982095153791, 371284982096667438, 371284982067047306, 371284981809967303, 371284981832170718, 371284982111932349, 371284982258962260]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 57940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 57900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362478530386759799, 362478579507069073⟩, ⟨369212635025323313, 371135809895243975⟩, true⟩

def words05 : List Nat := [371284982386843119, 371284982515392491, 371284982698023993, 371284982769693692, 371284982907630322, 371284983046292571, 371284983182918036, 371284983184874220, 371284982924389760, 371284982816418543]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 57950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 57900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470417624680487, 362470466762404558⟩, ⟨839487227161022856, 841411411482951688⟩, true⟩

def words06 : List Nat := [371284982857282888, 371284982859239399, 371284982660728737, 371284982464604871, 371284982267756369, 371284982161262227, 371284981906080499, 371284981726077562, 371284981545413877, 371284981363258154]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 57960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 57900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507107323015971, 362507156478386996⟩, ⟨(-1287588209557488353), (-1285663002150010103)⟩, true⟩

def words07 : List Nat := [371284981114210128, 371284981085434014, 371284981322429985, 371284981376223013, 371284981380875089, 371284981386151139, 371284981688434033, 371284981842637304, 371284982226419022, 371284982611048558]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 57970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 57900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485166482556775, 362485215655605742⟩, ⟨(-15422974357350295), (-13496741893868287)⟩, true⟩

def words08 : List Nat := [371284982886824382, 371284982888782057, 371284982946230239, 371284983082171290, 371284983306678818, 371284983308636337, 371284983176718042, 371284983003786632, 371284982910798997, 371284982917044692]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 57980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 57900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476486542085729, 362476535732771168⟩, ⟨488048591164977377, 489975846455953805⟩, true⟩

def words09 : List Nat := [371284983220036717, 371284983523845668, 371284983823115319, 371284983825073129, 371284983765349046, 371284983723646050, 371284983876538671, 371284983878497124, 371284983735618479, 371284983592192823]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 57990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 57900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 57900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk579
