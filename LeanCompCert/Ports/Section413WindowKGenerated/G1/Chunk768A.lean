import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk768A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482567256911424, 362482655424468645⟩, ⟨190867722636243320, 195440320822405124⟩, true⟩

def state01 : KState := ⟨⟨362485727458938747, 362485815650070750⟩, ⟨(-51812590618674055), (-47238181765465331)⟩, true⟩

def words00 : List Nat := [371285200325205491, 371285200327870703, 371285200313691959, 371285200300538503, 371285200322102817, 371285200325055353, 371285200409736660, 371285200528735090, 371285200646916483, 371285200657663863]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 76800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 76800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493982868789045, 362494071083852766⟩, ⟨(-685985740514680767), (-681409493345492273)⟩, true⟩

def words01 : List Nat := [371285200738085443, 371285200819819223, 371285200988133401, 371285200990781191, 371285200950036051, 371285200877616039, 371285200804983064, 371285200807954486, 371285200871404108, 371285200989824500]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 76810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 76800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480939393036515, 362481027631978997⟩, ⟨316019874547596889, 320597956203577883⟩, true⟩

def words02 : List Nat := [371285201095037780, 371285201097686399, 371285201006087705, 371285201016401459, 371285201034709048, 371285201037357562, 371285200848826249, 371285200661262255, 371285200472649047, 371285200454524925]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 76820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 76800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362473643381728314, 362473731644567295⟩, ⟨876675953253095873, 881255870996763841⟩, true⟩

def words03 : List Nat := [371285200516941076, 371285200634833183, 371285200750777322, 371285200753427228, 371285200672457738, 371285200598280332, 371285200614655179, 371285200617304299, 371285200503347480, 371285200357099789]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 76830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 76800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488649108983429, 362488737395542802⟩, ⟨(-276424427426402916), (-271842686887406174)⟩, true⟩

def words04 : List Nat := [371285200209644366, 371285200204295463, 371285200112886449, 371285200092649591, 371285200071612811, 371285200028417951, 371285199920846461, 371285199953961432, 371285200077414587, 371285200126191884]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 76840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 76800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk768A
