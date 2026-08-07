import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk454

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470285208714641, 362470314758840912⟩, ⟨691022721674295655, 691929149485731643⟩, true⟩

def state01 : KState := ⟨⟨362485108593493454, 362485138157104703⟩, ⟨18100908777594699, 19007948873021007⟩, true⟩

def words00 : List Nat := [371285555247406670, 371285555249094527, 371285555673632425, 371285556129381867, 371285556503017031, 371285556504520873, 371285556410147365, 371285556515665647, 371285556740633409, 371285556742193297]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 45400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 45400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486222459882511, 362486252037164962⟩, ⟨(-32408365451080630), (-31500704475117402)⟩, true⟩

def words01 : List Nat := [371285556734100378, 371285556725769505, 371285557191471130, 371285557471649021, 371285557884407133, 371285558297762693, 371285558709855723, 371285558711359743, 371285558492729264, 371285558509843347]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 45410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 45400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488207361274371, 362488236951981372⟩, ⟨(-122573961391914123), (-121665690604567129)⟩, true⟩

def words02 : List Nat := [371285558937314455, 371285558938825801, 371285558905333074, 371285558770669145, 371285558635415145, 371285558554033043, 371285558472698756, 371285558675262020, 371285558859023451, 371285558919567282]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 45420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 45400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362518533946001476, 362518563550307291⟩, ⟨(-1500441911479101491), (-1499533022828617831)⟩, true⟩

def words03 : List Nat := [371285559418678519, 371285559918575959, 371285560901789094, 371285561240021430, 371285561522784340, 371285561805984146, 371285562290806142, 371285562534724800, 371285563262001100, 371285563989936071]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 45430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 45400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491004784654074, 362491034402556731⟩, ⟨(-249480702144404171), (-248571195585443737)⟩, true⟩

def words04 : List Nat := [371285564573693501, 371285564575198593, 371285564810629658, 371285565109443181, 371285565498133900, 371285565499640356, 371285565346943734, 371285565194163760, 371285565287607966, 371285565409672407]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 45440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 45400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362479743592313403, 362479773223767486⟩, ⟨262392975605801438, 263303098147888334⟩, true⟩

def words05 : List Nat := [371285565655964452, 371285565902836153, 371285566154766063, 371285566156271607, 371285565763279781, 371285565517801987, 371285565447502848, 371285565449038756, 371285565322624253, 371285565196889965]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 45450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 45400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481414514307906, 362481444159224668⟩, ⟨186465281845017455, 187376016470929993⟩, true⟩

def words06 : List Nat := [371285565248890180, 371285565250549021, 371285565375746127, 371285565564408463, 371285565632224128, 371285565633730216, 371285565121552869, 371285564967086506, 371285565028931873, 371285565030490798]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 45460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 45400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470262433881586, 362470292092560772⟩, ⟨693691284351764308, 694602644822289462⟩, true⟩

def words07 : List Nat := [371285564940992452, 371285564822770043, 371285564957927638, 371285565102090430, 371285565276170181, 371285565450800262, 371285565612727617, 371285565614234157, 371285565131972275, 371285564798031799]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 45470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 45400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362456017759193869, 362456047431292773⟩, ⟨1341664551830975297, 1342576522700405595⟩, true⟩

def words08 : List Nat := [371285564610494127, 371285564612000761, 371285564116367179, 371285563620616692, 371285563124332793, 371285562646173089, 371285562030965681, 371285561732718019, 371285561433956575, 371285561094135165]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 45480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 45400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488055379190194, 362488085064915319⟩, ⟨(-115901697591416141), (-114989106798507893)⟩, true⟩

def words09 : List Nat := [371285560446377805, 371285560282252462, 371285560117384654, 371285560050745672, 371285559518381562, 371285558901543999, 371285558284096810, 371285558150061874, 371285557830081567, 371285557887341233]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 45490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 45400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 45400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk454
