import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk761A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk761B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk761A

def state06 : KState := ⟨⟨362494673701280284, 362494760349283274⟩, ⟨(-732267989397370068), (-727811607614003504)⟩, true⟩

def words05 : List Nat := [371285204182403665, 371285204214795115, 371285204237649506, 371285204240287858, 371285204136225163, 371285204005665486, 371285203913003103, 371285203915920971, 371285203996346714, 371285204124869020]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 76150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 76100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484434910932070, 362484521582568601⟩, ⟨47539530579608934, 51997712416738672⟩, true⟩

def words06 : List Nat := [371285204251209663, 371285204253833388, 371285204257942905, 371285204348390493, 371285204489939832, 371285204492563589, 371285204404599413, 371285204301907048, 371285204233014320, 371285204236007183]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 76160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 76100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475161566126450, 362475248261377894⟩, ⟨753993969911115680, 758453950614126932⟩, true⟩

def words07 : List Nat := [371285204339652496, 371285204453297711, 371285204566043185, 371285204568712970, 371285204538094179, 371285204516308489, 371285204577191863, 371285204579817121, 371285204466195942, 371285204338440301]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 76170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 76100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482678993575644, 362482765712326568⟩, ⟨181268084616313273, 185729855631441885⟩, true⟩

def words08 : List Nat := [371285204209561412, 371285204153485911, 371285204010227627, 371285203951260968, 371285203891473507, 371285203805904926, 371285203564804667, 371285203472313267, 371285203429194517, 371285203431917479]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 76180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 76100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478571088298310, 362478657830982383⟩, ⟨494292137516996105, 498755732116491769⟩, true⟩

def words09 : List Nat := [371285203401884470, 371285203369736212, 371285203415501564, 371285203432146448, 371285203454905077, 371285203478613540, 371285203480588656, 371285203470288353, 371285203264415846, 371285203181797561]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 76190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 76100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 76100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk761B
