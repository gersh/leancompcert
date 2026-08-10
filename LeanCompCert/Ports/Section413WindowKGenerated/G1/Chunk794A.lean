import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk794A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362506027306692088, 362506121786961786⟩, ⟨(-1666362228626192458), (-1661296558462953552)⟩, true⟩

def state01 : KState := ⟨⟨362492661935675044, 362492756440727094⟩, ⟨(-605096767810509338), (-600029129801380342)⟩, true⟩

def words00 : List Nat := [371285199161021369, 371285199251592556, 371285199491168906, 371285199732147550, 371285200020506129, 371285200098392230, 371285200153905233, 371285200210405195, 371285200347309076, 371285200445590383]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 79400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 79400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477643835789496, 362477738365501029⟩, ⟨587641288354785092, 592710884700326320⟩, true⟩

def words01 : List Nat := [371285200701021499, 371285200957538177, 371285201206776722, 371285201265875621, 371285201330779962, 371285201397061723, 371285201527252958, 371285201529996604, 371285201449142919, 371285201358257266]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 79410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 79400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492099946654539, 362492194500949548⟩, ⟨(-560489410407038629), (-555417861519279253)⟩, true⟩

def words02 : List Nat := [371285201303302171, 371285201306381524, 371285201441996070, 371285201591089120, 371285201711415926, 371285201714160085, 371285201719314503, 371285201803403442, 371285201952940890, 371285202043829290]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 79420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 79400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489039313661931, 362489133892976383⟩, ⟨(-317339508788447892), (-312265972478476978)⟩, true⟩

def words03 : List Nat := [371285202095539560, 371285202148184053, 371285202358041263, 371285202489743341, 371285202669003887, 371285202849337898, 371285203028709240, 371285203031453597, 371285203048997999, 371285203101917881]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 79430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 79400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487867109534132, 362487961713317059⟩, ⟨(-224202023089540618), (-219126542875892618)⟩, true⟩

def words04 : List Nat := [371285203253798565, 371285203297233165, 371285203303180609, 371285203309964330, 371285203364426013, 371285203367450659, 371285203451770152, 371285203563904583, 371285203667088734, 371285203704696955]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 79440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 79400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk794A
