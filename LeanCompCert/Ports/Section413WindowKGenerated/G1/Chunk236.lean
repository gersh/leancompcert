import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk236

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362531339319709949, 362531346883053267⟩, ⟨(-1102481123691103162), (-1102360432410792850)⟩, true⟩

def state01 : KState := ⟨⟨362531580775193001, 362531588345223954⟩, ⟨(-1108348189612775307), (-1108227340469510155)⟩, true⟩

def words00 : List Nat := [371284640648702620, 371284640649444218, 371284641612515630, 371284642992491949, 371284644912036909, 371284645705243902, 371284646354587039, 371284647004129303, 371284649448128198, 371284651436983325]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 23600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 23600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479986020309625, 362479993597023541⟩, ⟨110141077594040519, 110262084556025527⟩, true⟩

def words01 : List Nat := [371284654154812896, 371284656872697459, 371284659396579695, 371284659532548793, 371284660209076342, 371284660885931090, 371284662151895773, 371284662152650987, 371284661959996117, 371284661763177480]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 23610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 23600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362519050476858010, 362519058060212151⟩, ⟨(-812756051870210747), (-812634888032224975)⟩, true⟩

def words02 : List Nat := [371284662066345458, 371284662067163681, 371284663376945877, 371284664928579565, 371284666036456414, 371284666037198916, 371284665273093209, 371284665787710021, 371284668093803313, 371284669549864209]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 23620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 23600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362506916304219821, 362506923894357162⟩, ⟨(-525766974805466166), (-525645650646266762)⟩, true⟩

def words03 : List Nat := [371284671001581217, 371284672453448604, 371284675696121882, 371284678258856197, 371284681095460143, 371284683932101967, 371284686764296209, 371284687518675555, 371284688459817405, 371284689401288076]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 23630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 23600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480265620944438, 362480273217703160⟩, ⟨104406385027548354, 104527865750512648⟩, true⟩

def words04 : List Nat := [371284691834941435, 371284691886063427, 371284691886624950, 371284691738246491, 371284691980099534, 371284691980932093, 371284692144417284, 371284692573722492, 371284692999834712, 371284693000610159]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 23640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 23600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362512741854399449, 362512749457875309⟩, ⟨(-663840616181166581), (-663718976563876817)⟩, true⟩

def words05 : List Nat := [371284694092035319, 371284695370611831, 371284697254038611, 371284697254782056, 371284696758051786, 371284696113999833, 371284696132856373, 371284696133675314, 371284697091156340, 371284698277597051]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 23650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 23600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468995719586607, 362469003329773299⟩, ⟨371252144838537728, 371373943267729012⟩, true⟩

def words06 : List Nat := [371284699101115253, 371284699101858942, 371284697778009255, 371284698009849083, 371284698781222258, 371284698781966012, 371284697175909494, 371284695181038680, 371284693186041786, 371284692976721662]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 23660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 23600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483008460138208, 362483016077029594⟩, ⟨39726579829402935, 39848536993002981⟩, true⟩

def words07 : List Nat := [371284693436647265, 371284694559612615, 371284695647694655, 371284695648742867, 371284696173135088, 371284696697840442, 371284699006401478, 371284699007145580, 371284698940197656, 371284698869976934]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 23670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 23600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362509074899637917, 362509082523201929⟩, ⟨(-577752029931831818), (-577629914726781324)⟩, true⟩

def words08 : List Nat := [371284699095495120, 371284699096314734, 371284698817410114, 371284699132451696, 371284699164831926, 371284699165579789, 371284697631314662, 371284697756442640, 371284699664062897, 371284700694037826]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 23680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 23600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502356630490634, 362502364260828135⟩, ⟨(-418544765272075587), (-418422489568362841)⟩, true⟩

def words09 : List Nat := [371284701616353106, 371284702538833913, 371284704253654056, 371284705352366377, 371284706565876263, 371284707779568289, 371284708979598566, 371284708980345763, 371284709302548604, 371284710048365861]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 23690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 23600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 23600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk236
