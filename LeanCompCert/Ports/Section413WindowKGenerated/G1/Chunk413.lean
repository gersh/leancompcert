import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk413

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492005257994084, 362492029524641225⟩, ⟨(-287464339182136268), (-286787135222479640)⟩, true⟩

def state01 : KState := ⟨⟨362469871843556727, 362469896122450798⟩, ⟨626686672865962686, 627364382686167164⟩, true⟩

def words00 : List Nat := [371285085849035943, 371285085850393149, 371285085298549328, 371285085254910370, 371285085210598505, 371285085191822585, 371285084569065456, 371285083837743166, 371285083105915242, 371285082866161430]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 41300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 41300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478032974519136, 362478057265643660⟩, ⟨289623412198041620, 290301627321279616⟩, true⟩

def words01 : List Nat := [371285082662668890, 371285082827358526, 371285082979114589, 371285082980502109, 371285082796281921, 371285082789061518, 371285083294042325, 371285083295400225, 371285083126962110, 371285082958463633]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 41310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 41300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362466541264357334, 362466565567661809⟩, ⟨764585198079966707, 765263916539074417⟩, true⟩

def words02 : List Nat := [371285082863646166, 371285082865142216, 371285082890840498, 371285083109764330, 371285083271665684, 371285083273023634, 371285082655073858, 371285082120426864, 371285081585041286, 371285081510476692]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 41320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 41300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362476884011553779, 362476908327200285⟩, ⟨337078725852198923, 337757954471213443⟩, true⟩

def words03 : List Nat := [371285081063501973, 371285080560295737, 371285080136867267, 371285080138363465, 371285079947393034, 371285079785579372, 371285079623314108, 371285079458167023, 371285078768799120, 371285078572833358]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 41330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 41300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474200914376255, 362474225242139746⟩, ⟨448125241509505249, 448804971107322195⟩, true⟩

def words04 : List Nat := [371285078763227120, 371285078764609090, 371285078665679334, 371285078566883357, 371285078543197995, 371285078544708436, 371285078633595820, 371285078938390582, 371285079048981074, 371285079050389017]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 41340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 41300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362525650553731639, 362525674893790212⟩, ⟨(-1679561073402910369), (-1678880835342561137)⟩, true⟩

def words05 : List Nat := [371285079110759690, 371285079434309508, 371285080140561681, 371285080409630227, 371285080580477362, 371285080751742587, 371285081506645390, 371285082013454240, 371285082995829358, 371285083978789546]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 41350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 41300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362498906232779841, 362498930585109137⟩, ⟨(-573408914316807495), (-572728168676283541)⟩, true⟩

def words06 : List Nat := [371285084882581635, 371285085008320786, 371285085284510329, 371285085561373350, 371285086013579314, 371285086035420584, 371285086056853884, 371285086078756543, 371285086537879099, 371285086874087497]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 41360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 41300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469385721026821, 362469410085576463⟩, ⟨648085511429350056, 648766762689489998⟩, true⟩

def words07 : List Nat := [371285087509628700, 371285088145673063, 371285088780244292, 371285088781604146, 371285088793928304, 371285088880983433, 371285089104417782, 371285089105781336, 371285088731750266, 371285088354370313]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 41370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 41300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362502066388080364, 362502090764795715⟩, ⟨(-704328340203786161), (-703646585464079781)⟩, true⟩

def words08 : List Nat := [371285088181079825, 371285088227257669, 371285088698269826, 371285089169848523, 371285089563587882, 371285089564948042, 371285089379708918, 371285089579897547, 371285090362675934, 371285090774810838]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 41380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 41300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362500826756757469, 362500851145911154⟩, ⟨(-653061597643214124), (-652379328020863262)⟩, true⟩

def words09 : List Nat := [371285091085044919, 371285091395719028, 371285091921259121, 371285092155653146, 371285092439985183, 371285092724809059, 371285093008948266, 371285093010332363, 371285093189411604, 371285093571745775]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 41390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 41300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 41300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk413
