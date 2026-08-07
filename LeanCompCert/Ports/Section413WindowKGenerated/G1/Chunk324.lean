import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk324

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362460667744457272, 362460682384383816⟩, ⟨781163307389130159, 781483908876685399⟩, true⟩

def state01 : KState := ⟨⟨362461095663510350, 362461110312751193⟩, ⟨767345595240815975, 767666498561120407⟩, true⟩

def words00 : List Nat := [371284801719542033, 371284801720589456, 371284800956185813, 371284799999768245, 371284799043020039, 371284798381006915, 371284797391581470, 371284797068162286, 371284796744413131, 371284796412675943]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 32400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 32400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492769955862945, 362492784614531511⟩, ⟨(-259262241579737065), (-258941032657995425)⟩, true⟩

def words01 : List Nat := [371284795900717167, 371284796120078621, 371284797287734088, 371284797471988966, 371284797498900463, 371284797526149645, 371284797643851236, 371284797645013230, 371284797536481330, 371284797784000128]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 32410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 32400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362500649887220699, 362500664555323094⟩, ⟨(-514841210685462840), (-514519695871849510)⟩, true⟩

def words02 : List Nat := [371284797961051423, 371284797962103202, 371284797988819228, 371284798477279587, 371284799245918471, 371284799246964905, 371284798949817642, 371284798653309723, 371284799006923676, 371284799497326984]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 32420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 32400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362466727077100016, 362466741754643663⟩, ⟨585474129680635825, 585795950722168079⟩, true⟩

def words03 : List Nat := [371284800204309674, 371284800911674116, 371284801563658560, 371284801564704629, 371284800951274289, 371284800514561368, 371284800497618667, 371284800498683173, 371284800138450711, 371284799582964322]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 32430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 32400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362502939215358710, 362502953902264987⟩, ⟨(-589341843461680711), (-589019718649169631)⟩, true⟩

def words04 : List Nat := [371284799418027181, 371284799419179537, 371284800199652226, 371284801064388782, 371284801680663150, 371284801681709486, 371284801208805043, 371284801385536564, 371284802291970046, 371284802852416010]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 32440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 32400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362477560850500632, 362477575546933219⟩, ⟨234382050608757682, 234704484599214744⟩, true⟩

def words05 : List Nat := [371284803324609077, 371284803797137332, 371284804630440339, 371284804995349830, 371284805652308236, 371284806309635205, 371284806958127921, 371284806959174586, 371284806344029322, 371284806122552419]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 32450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 32400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362454602729087129, 362454617434841827⟩, ⟨979647280204224719, 979970016839537797⟩, true⟩

def words06 : List Nat := [371284805905999000, 371284805907045860, 371284804650084946, 371284803390288179, 371284802130155918, 371284801057788316, 371284799642481193, 371284799173772965, 371284798704750663, 371284798217620994]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 32460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 32400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497448765080129, 362497463480334739⟩, ⟨(-411819510876369618), (-411496465733368192)⟩, true⟩

def words07 : List Nat := [371284797288864846, 371284797063564501, 371284797004445310, 371284797005497630, 371284796269829115, 371284795384248651, 371284794498305876, 371284794417504367, 371284794252960494, 371284794644223371]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 32470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 32400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362461860321022757, 362461875045728696⟩, ⟨744162992660130836, 744486344830412276⟩, true⟩

def words08 : List Nat := [371284795022176372, 371284795023224033, 371284794271150766, 371284794011072047, 371284793750504585, 371284793694051826, 371284792553360056, 371284791225082256, 371284789896451258, 371284789368438158]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 32480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 32400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362467102285980379, 362467117020111899⟩, ⟨574005269767523020, 574328928223445850⟩, true⟩

def words09 : List Nat := [371284788903433191, 371284789144080569, 371284789385834489, 371284789386907673, 371284789115891654, 371284788985651623, 371284789667798542, 371284789668846642, 371284789222028230, 371284788679441852]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 32490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 32400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 32400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk324
