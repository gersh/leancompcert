import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk729A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk729A
