import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk856

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362460047087738980, 362460157536272547⟩, ⟨2143419366832187577, 2149803090345338441⟩, true⟩

def state01 : KState := ⟨⟨362475125624368885, 362475236099566176⟩, ⟨852639654359687821, 859025660424410255⟩, true⟩

def words00 : List Nat := [371285271766982972, 371285271613251196, 371285271410491813, 371285271266157813, 371285271120938518, 371285270965571089, 371285270662010192, 371285270496398440, 371285270329182607, 371285270273849840]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 85600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 85600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478489357767288, 362478599860028175⟩, ⟨564641443966961373, 571029767086068235⟩, true⟩

def words01 : List Nat := [371285270158867345, 371285270044793679, 371285269929543984, 371285269866453208, 371285269749804972, 371285269676177790, 371285269601570503, 371285269496675513, 371285269284504735, 371285269210262771]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 85610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 85600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477258279199736, 362477368807958913⟩, ⟨670083684896138521, 676474276935701045⟩, true⟩

def words02 : List Nat := [371285269192780069, 371285269195758668, 371285269102091729, 371285269009468083, 371285268915602812, 371285268857288629, 371285268756300784, 371285268776136322, 371285268778370564, 371285268776158560]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 85620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 85600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487823891716555, 362487934447440255⟩, ⟨(-234741452186405962), (-228348551038729010)⟩, true⟩

def words03 : List Nat := [371285268685966217, 371285268629425235, 371285268611686163, 371285268614663768, 371285268500664036, 371285268346152568, 371285268190461185, 371285268138723492, 371285268066779231, 371285268101285508]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 85630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 85600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482664462636642, 362482775045214388⟩, ⟨207099430001888507, 213494631064140931⟩, true⟩

def words04 : List Nat := [371285268134582240, 371285268137559165, 371285267988935808, 371285267978098577, 371285267965803502, 371285267961623745, 371285267866191106, 371285267771753228, 371285267681989776, 371285267685390269]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 85640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 85600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362465896534451446, 362466007143830906⟩, ⟨1643428272180369771, 1649825768945029537⟩, true⟩

def words05 : List Nat := [371285267743141902, 371285267831247457, 371285267918959503, 371285267921936908, 371285267844673646, 371285267793835418, 371285267741449325, 371285267727289135, 371285267530769734, 371285267309240024]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487731077055651, 362487841713093355⟩, ⟨(-227022306454433792), (-220622526009270844)⟩, true⟩

def words06 : List Nat := [371285267086417405, 371285267001054797, 371285266846145946, 371285266778928907, 371285266710744052, 371285266621333639, 371285266442468308, 371285266401287198, 371285266449974687, 371285266483132117]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478207893121470, 362478318556389456⟩, ⟨588898810613846214, 595300924003581786⟩, true⟩

def words07 : List Nat := [371285266508190959, 371285266534253775, 371285266615368346, 371285266637643242, 371285266670174823, 371285266703814215, 371285266736432086, 371285266739410177, 371285266590269313, 371285266513018817]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472067897542610, 362472178587300018⟩, ⟨1115005530660179701, 1121409913803240235⟩, true⟩

def words08 : List Nat := [371285266468028538, 371285266471006704, 371285266325778715, 371285266180353138, 371285266033814329, 371285265930231914, 371285265757492741, 371285265642234628, 371285265525967521, 371285265410894408]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493413676238941, 362493524392891791⟩, ⟨(-714202834430488170), (-707796146482902530)⟩, true⟩

def words09 : List Nat := [371285265260193189, 371285265247062250, 371285265331165045, 371285265334195815, 371285265322321403, 371285265293255639, 371285265305160447, 371285265308482321, 371285265391360366, 371285265491053039]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk856
