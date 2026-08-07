import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk729

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362495114370124662, 362495193490134776⟩, ⟨(-726296523509653642), (-722401299392195180)⟩, true⟩

def state01 : KState := ⟨⟨362491785827924205, 362491864970211044⟩, ⟨(-483618442135945483), (-479721593927741519)⟩, true⟩

def words00 : List Nat := [371285284468822101, 371285284544571659, 371285284612418705, 371285284681140806, 371285284756672760, 371285284759434287, 371285284948321601, 371285285138599931, 371285285327045658, 371285285419883553]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 72900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 72900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362495540638142019, 362495619803122733⟩, ⟨(-757347862894603526), (-753449359964118182)⟩, true⟩

def words01 : List Nat := [371285285699755581, 371285285981007917, 371285286380558399, 371285286530324308, 371285286648349827, 371285286767129338, 371285286984420978, 371285287109398645, 371285287252837736, 371285287397369053]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 72910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 72900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362498379941141737, 362498459128727396⟩, ⟨(-964453953918140207), (-960553802524488931)⟩, true⟩

def words02 : List Nat := [371285287530615784, 371285287533125779, 371285287613961013, 371285287750439180, 371285287944163713, 371285287982135842, 371285288005678257, 371285288030082440, 371285288224930994, 371285288408422938]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 72920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 72900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487013247492176, 362487092457613819⟩, ⟨(-135362058523991546), (-131460263463346622)⟩, true⟩

def words03 : List Nat := [371285288778556044, 371285289149675821, 371285289475180039, 371285289550823227, 371285289661658042, 371285289773777630, 371285290072361695, 371285290121315772, 371285290147899277, 371285290175447914]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 72930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 72900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478680666275345, 362478759898799894⟩, ⟨472470348566511541, 476373777812269807⟩, true⟩

def words04 : List Nat := [371285290259966109, 371285290262727149, 371285290342777719, 371285290435229879, 371285290499894020, 371285290502399783, 371285290316457519, 371285290162154516, 371285290037091368, 371285290039688342]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 72940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 72900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362487336151623174, 362487415407021899⟩, ⟨(-158969998235509648), (-155064900211443322)⟩, true⟩

def words05 : List Nat := [371285289952047454, 371285289865800427, 371285289877246189, 371285289911940685, 371285290002625896, 371285290094263219, 371285290187847644, 371285290190353739, 371285290062586582, 371285290094865933]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 72950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 72900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472480319582417, 362472559597317813⟩, ⟨924973550367436789, 928880278191477201⟩, true⟩

def words06 : List Nat := [371285290201583572, 371285290204089736, 371285290070869341, 371285289890953352, 371285289710093799, 371285289587317300, 371285289369384565, 371285289319301619, 371285289268312508, 371285289216040459]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 72960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 72900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497703068960152, 362497782369313020⟩, ⟨(-915626350631056023), (-911717972294438529)⟩, true⟩

def words07 : List Nat := [371285289043293445, 371285289028403399, 371285289181976695, 371285289222000305, 371285289223976131, 371285289219549801, 371285289394524678, 371285289483678597, 371285289656567242, 371285289830538621]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 72970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 72900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483781500382377, 362483860823388069⟩, ⟨100442682490536980, 104352714147336220⟩, true⟩

def words08 : List Nat := [371285289980102378, 371285290021720886, 371285290216104296, 371285290411803944, 371285290614338202, 371285290616845264, 371285290569356364, 371285290523165690, 371285290505583810, 371285290508470236]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 72980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 72900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482496986678591, 362482576332295156⟩, ⟨194232710115271357, 198144392251839811⟩, true⟩

def words09 : List Nat := [371285290629396117, 371285290770960566, 371285290897375558, 371285290899882806, 371285290776129302, 371285290691443442, 371285290705214468, 371285290707734426, 371285290673377356, 371285290639038332]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 72990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 72900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 72900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk729
