import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk837A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589232231511708, 360589278023269833⟩, ⟨(-573548685965570273), (-570960259204500557)⟩, true⟩

def state01 : KState := ⟨⟨360589874166166792, 360589919969230896⟩, ⟨(-627301446172001779), (-624712073042449661)⟩, true⟩

def words00 : List Nat := [360582456821395469, 360582456904287888, 360582456915537824, 360582456926918589, 360582456927923551, 360582456989126587, 360582457073484916, 360582457158069763, 360582457159149943, 360582457245418704]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360612914399045679, 360612960213455695⟩, ⟨(-2556175936252803358), (-2553585613299826610)⟩, true⟩

def words01 : List Nat := [360582457439984669, 360582457634898803, 360582457825796145, 360582457955652428, 360582457964051374, 360582457972543626, 360582458123380779, 360582458346482183, 360582458711784998, 360582459077381117]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592458053082512, 360592503878921708⟩, ⟨(-843576138674661662), (-840984858813995564)⟩, true⟩

def words02 : List Nat := [360582459314149098, 360582459467576991, 360582459698968318, 360582459930706129, 360582460077103429, 360582460081334957, 360582460082435081, 360582459976094403, 360582459869526097, 360582459990053619]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578777567650839, 360578823404802115⟩, ⟨301978124015412166, 304570351093662498⟩, true⟩

def words03 : List Nat := [360582460125526449, 360582460261233200, 360582460299586483, 360582460341573861, 360582460347469429, 360582460353695974, 360582460502060320, 360582460541109583, 360582460542180104, 360582460499990719]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592865505689963, 360592911354200607⟩, ⟨(-877871811960981826), (-875278633594217426)⟩, true⟩

def words04 : List Nat := [360582460457546600, 360582460465703831, 360582460484905023, 360582460504328111, 360582460505446684, 360582460403080523, 360582460259189931, 360582460225567324, 360582460264792590, 360582460390825911]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk837A
