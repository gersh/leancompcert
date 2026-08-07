import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk256

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362424115790569003, 362424124751375103⟩, ⟨1573923110917048805, 1574078200240576553⟩, true⟩

def state01 : KState := ⟨⟨362503392948649019, 362503401916699171⟩, ⟨(-455883711263297642), (-455728436455291318)⟩, true⟩

def words00 : List Nat := [371285609779862868, 371285608903594019, 371285607432533931, 371285607459773117, 371285607460405735, 371285607194973771, 371285605918555493, 371285605763328722, 371285606974957258, 371285607670615251]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 25600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 25600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362465291742524637, 362465300717952655⟩, ⟨520213821277764135, 520369285070637855⟩, true⟩

def words01 : List Nat := [371285608357166218, 371285609043930303, 371285610361663618, 371285610915383968, 371285611839445239, 371285612763753509, 371285613679435236, 371285613680245077, 371285612566939745, 371285611775137302]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 25610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 25600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362450561999866760, 362450570982502653⟩, ⟨897759644652450542, 897915293149085858⟩, true⟩

def words02 : List Nat := [371285611712174213, 371285611712985500, 371285610807804031, 371285609936193091, 371285609064334945, 371285608438687838, 371285607056555014, 371285606288328072, 371285605519895619, 371285604743452676]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 25620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 25600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362528612783755004, 362528621773725481⟩, ⟨(-1103087243400284634), (-1102931406881519504)⟩, true⟩

def words03 : List Nat := [371285603377153333, 371285603002658637, 371285603772934340, 371285603773758774, 371285603659046875, 371285603318250074, 371285603890425966, 371285604048989052, 371285605727298079, 371285607405842734]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 25630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 25600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468928590325987, 362468937587629628⟩, ⟨427364285088206032, 427520309666076426⟩, true⟩

def words04 : List Nat := [371285608503337724, 371285608504148520, 371285608167425787, 371285608759572378, 371285609454842491, 371285609455653423, 371285608126107249, 371285606769419254, 371285605412485226, 371285605046096142]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 25640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 25600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362441255811612387, 362441264816199365⟩, ⟨1137465480326813182, 1137621691760516646⟩, true⟩

def words05 : List Nat := [371285605069000804, 371285605741958590, 371285606239749312, 371285606240560503, 371285604930026061, 371285603689674756, 371285602726109355, 371285602726920574, 371285600981622555, 371285599254693540]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 25650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 25600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362461898030136964, 362461907042004983⟩, ⟨607840927106913317, 607997325408133653⟩, true⟩

def words06 : List Nat := [371285597527547461, 371285597059801217, 371285596262944608, 371285596235020408, 371285596206835902, 371285595794548960, 371285593646377030, 371285593015728167, 371285592384718276, 371285592173497314]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 25660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 25600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488778280300332, 362488787299573089⟩, ⟨(-82266321183678575), (-82109732765664147)⟩, true⟩

def words07 : List Nat := [371285591251463606, 371285590344114062, 371285590044869639, 371285590116121278, 371285590457538721, 371285590799243983, 371285591144669536, 371285591145482153, 371285589879057237, 371285590004578126]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 25670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 25600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362451847668176678, 362451856694694463⟩, ⟨866308344045817606, 866465118554098888⟩, true⟩

def words08 : List Nat := [371285591381947174, 371285591382759446, 371285590740777897, 371285589808525462, 371285588876046979, 371285588025421492, 371285586412470325, 371285585749817619, 371285585086930344, 371285584414373486]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 25680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 25600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362498606836235824, 362498615870083372⟩, ⟨(-335123273989618943), (-334966311142138027)⟩, true⟩

def words09 : List Nat := [371285583102103960, 371285582881702992, 371285583953547703, 371285583954361098, 371285583625471923, 371285583008193902, 371285582396904553, 371285582397799709, 371285582160573039, 371285582668607082]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 25690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 25600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 25600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk256
