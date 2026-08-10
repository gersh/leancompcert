import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk972A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490435967682470, 362490579783309327⟩, ⟨(-519353040605264268), (-509915151133693104)⟩, true⟩

def state01 : KState := ⟨⟨362485390995000664, 362485534841030055⟩, ⟨(-28919612649680466), (-19478767891912768)⟩, true⟩

def words00 : List Nat := [371285333922452719, 371285333974420680, 371285334025132563, 371285334076973575, 371285334159386652, 371285334199726878, 371285334292801990, 371285334387282792, 371285334459266697, 371285334464859746]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 97200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 97200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362506937952956673, 362507081829796307⟩, ⟨(-2123613491746986447), (-2114169651769874617)⟩, true⟩

def words01 : List Nat := [371285334549671370, 371285334636213679, 371285334826937179, 371285334917784080, 371285334991758800, 371285335066913894, 371285335229848228, 371285335357952375, 371285335583948449, 371285335811428158]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 97210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 97200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486117639915322, 362486261547561306⟩, ⟨(-99403937573458105), (-89957102444386797)⟩, true⟩

def words02 : List Nat := [371285336028407458, 371285336105190553, 371285336181723941, 371285336260003947, 371285336369175011, 371285336372587066, 371285336353170151, 371285336333913524, 371285336344562553, 371285336358038990]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 97220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 97200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475944707274793, 362476088645670150⟩, ⟨889823237753953520, 899273062794644064⟩, true⟩

def words03 : List Nat := [371285336475744012, 371285336594882493, 371285336712489372, 371285336715902427, 371285336727320122, 371285336751831554, 371285336800406407, 371285336803818933, 371285336711584915, 371285336620400659]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 97230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 97200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486837522242022, 362486981491157894⟩, ⟨(-169413264217809311), (-159960471206214735)⟩, true⟩

def words04 : List Nat := [371285336538362371, 371285336542131575, 371285336572575782, 371285336634751239, 371285336678392778, 371285336681805628, 371285336584119071, 371285336576342634, 371285336649870076, 371285336670321027]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 97240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 97200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk972A
