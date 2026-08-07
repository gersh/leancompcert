import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk124

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362362991025262407, 362362992998675029⟩, ⟨1507157512012242046, 1507174071229166410⟩, true⟩

def state01 : KState := ⟨⟨362467561407412434, 362467563384130713⟩, ⟨210175585706775185, 210192185930611353⟩, true⟩

def words00 : List Nat := [371284529493662712, 371284526168570702, 371284520563350639, 371284520466696087, 371284520369939594, 371284519181385771, 371284509363640048, 371284504322651367, 371284500707352050, 371284500707735114]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 12400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 12400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362485154230248950, 362485156210336930⟩, ⟨(-8137786443784079), (-8121144385039647)⟩, true⟩

def words01 : List Nat := [371284499343316424, 371284496963383345, 371284498665346189, 371284499497133366, 371284501523092271, 371284503548869474, 371284505599372977, 371284505599748792, 371284502333519806, 371284502386620238]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 12410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 12400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362433184092681173, 362433186076061057⟩, ⟨637656035356723653, 637672718318139213⟩, true⟩

def words02 : List Nat := [371284508893647658, 371284508894017319, 371284506792165459, 371284503779824996, 371284500767830354, 371284497903513563, 371284492769391824, 371284490930800373, 371284489092384804, 371284487179706925]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 12420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 12400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362532332157114174, 362532334143844820⟩, ⟨(-595111310238577193), (-595094585610288801)⟩, true⟩

def words03 : List Nat := [371284484175249851, 371284485297683414, 371284492860504375, 371284492860874469, 371284491830735299, 371284489725935944, 371284491954432602, 371284493112089620, 371284496958087780, 371284500803630184]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 12430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 12400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362462023156753266, 362462025146826554⟩, ⟨279513034891185688, 279529801118848890⟩, true⟩

def words04 : List Nat := [371284503295572133, 371284503295942451, 371284497206628520, 371284495597353624, 371284493988159142, 371284493649328241, 371284488273251097, 371284482943500558, 371284477614451599, 371284477339687506]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 12440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 12400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362438287472939931, 362438289466352439⟩, ⟨575508206495320919, 575525014313362741⟩, true⟩

def words05 : List Nat := [371284480154504733, 371284484771973492, 371284487948059734, 371284487948432114, 371284485059434249, 371284483471233275, 371284486712709629, 371284486713080416, 371284482981809987, 371284479274884812]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 12450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 12400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362436279858608652, 362436281855341310⟩, ⟨600693841356758425, 600710690560682379⟩, true⟩

def words06 : List Nat := [371284475874023330, 371284475874431995, 371284474132005917, 371284474648932249, 371284474649222385, 371284474200978418, 371284467004308618, 371284461188931235, 371284455374300023, 371284454324512175]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 12460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 12400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362518601221294154, 362518603221417240⟩, ⟨(-426203767420787930), (-426186875921604920)⟩, true⟩

def words07 : List Nat := [371284450462031129, 371284446631615788, 371284445370654379, 371284446209382246, 371284448979347420, 371284451749006343, 371284454551704223, 371284454552076718, 371284453631533867, 371284456368126510]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 12470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 12400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362435684578705946, 362435686582140352⟩, ⟨609007453534925584, 609024386376958500⟩, true⟩

def words08 : List Nat := [371284461775462032, 371284461775833658, 371284459290389969, 371284456828602260, 371284454367072630, 371284451838306031, 371284446736337131, 371284447379283096, 371284447541433576, 371284447541818251]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 12480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 12400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362523530994564163, 362523533001356000⟩, ⟨(-488602367491026227), (-488585392697635843)⟩, true⟩

def words09 : List Nat := [371284446120134387, 371284448601931739, 371284454686346211, 371284454686718075, 371284452258212297, 371284447565543052, 371284444560914947, 371284444561324255, 371284446169525913, 371284449296636567]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 12490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 12400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 12400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk124
