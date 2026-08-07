import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk291

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362475378092264025, 362475389795974029⟩, ⟨291218857830615649, 291449076870304791⟩, true⟩

def state01 : KState := ⟨⟨362469671792007250, 362469683504010839⟩, ⟨457349550093069275, 457580010517882863⟩, true⟩

def words00 : List Nat := [371285405720457833, 371285405721387937, 371285404985791384, 371285404225459333, 371285403464809989, 371285403061183383, 371285402386258399, 371285402434177066, 371285402500317208, 371285402501280434]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 29100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 29100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491622934907849, 362491634655343916⟩, ⟨(-181758556594457388), (-181527850658841786)⟩, true⟩

def words01 : List Nat := [371285402406000982, 371285402851146626, 371285403789611790, 371285403790542290, 371285403158385629, 371285402355760189, 371285401552824679, 371285401344931208, 371285400868182373, 371285401083328572]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 29110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 29100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362458846286520103, 362458858015345620⟩, ⟨772734871472421261, 772965821753018217⟩, true⟩

def words02 : List Nat := [371285401123174683, 371285401124105498, 371285399594167789, 371285399242556285, 371285398890511320, 371285398860805867, 371285397261544134, 371285395468281677, 371285393674750342, 371285393059003465]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 29120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 29100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362467169858975056, 362467181596175567⟩, ⟨530398211326094773, 530629405613620507⟩, true⟩

def words03 : List Nat := [371285392415043357, 371285392682320564, 371285392934088659, 371285392935035844, 371285392207317418, 371285391837001465, 371285392271521809, 371285392272455561, 371285391877083530, 371285391253197312]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 29130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 29100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362511218396505761, 362511230142059428⟩, ⟨(-753459402140988931), (-753227964400248105)⟩, true⟩

def words04 : List Nat := [371285390628961037, 371285390295003189, 371285389507684137, 371285389637178085, 371285389637900299, 371285389517547997, 371285388859431037, 371285389119175869, 371285390416751184, 371285391304132762]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 29140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 29100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362506861363721698, 362506873117774446⟩, ⟨(-626354447126539992), (-626122761595374122)⟩, true⟩

def words05 : List Nat := [371285392107770507, 371285392911672434, 371285394890612670, 371285396383154930, 371285397733240796, 371285399083568513, 371285400436722181, 371285400437654489, 371285401142609538, 371285401880107858]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 29150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 29100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492069031044319, 362492080793406764⟩, ⟨(-194872939268068743), (-194641011381873367)⟩, true⟩

def words06 : List Nat := [371285403192134683, 371285403527138184, 371285403865314076, 371285404203773211, 371285404799615452, 371285404807335646, 371285405989066915, 371285407171106981, 371285408148925191, 371285408378632438]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 29160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 29100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362559110146207447, 362559121916994435⟩, ⟨(-2150798513612926441), (-2150566339940600043)⟩, true⟩

def words07 : List Nat := [371285409572920981, 371285410767613963, 371285413135707766, 371285414245877216, 371285415169106599, 371285416092586992, 371285418024503427, 371285419377883279, 371285421904306433, 371285424430961037]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 29170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 29100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482827403493269, 362482839182711655⟩, ⟨75396092283927882, 75628512026486128⟩, true⟩

def words08 : List Nat := [371285426894396069, 371285427794434345, 371285428821149792, 371285429848277340, 371285431104740239, 371285431105673325, 371285430798979261, 371285430356358094, 371285430086461041, 371285430087542984]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 29180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 29100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362467720962261311, 362467732749889566⟩, ⟨516611295315842550, 516843960585474790⟩, true⟩

def words09 : List Nat := [371285431083431683, 371285432168390060, 371285433128425158, 371285433129364896, 371285433320012618, 371285433593399376, 371285434098126562, 371285434099064591, 371285433490654238, 371285432885526055]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 29190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 29100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 29100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk291
