import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk904A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362472053374713338, 362472177076628840⟩, ⟨1162288961935332890, 1169839295536063038⟩, true⟩

def state01 : KState := ⟨⟨362485953472598824, 362486077202729748⟩, ⟨(-94292466398482989), (-86739581978343691)⟩, true⟩

def words00 : List Nat := [371285117635792404, 371285117618451082, 371285117636481428, 371285117708971376, 371285117740516152, 371285117743679954, 371285117676036586, 371285117706096686, 371285117796941562, 371285117810819712]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 90400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 90400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481758781459149, 362481882540341975⟩, ⟨284999419356497249, 292554903383821885⟩, true⟩

def words01 : List Nat := [371285117823677712, 371285117837631729, 371285117938368317, 371285117979219357, 371285118040548205, 371285118103115209, 371285118164476015, 371285118167632263, 371285118083211034, 371285118051328304]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 90410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 90400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478218550187923, 362478342337158905⟩, ⟨605138933575990681, 612696957480460743⟩, true⟩

def words02 : List Nat := [371285118071734471, 371285118074893059, 371285117998862745, 371285117913536424, 371285117826976943, 371285117778656588, 371285117690961195, 371285117701159516, 371285117706638104, 371285117709905565]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 90420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 90400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489702575231649, 362489826390811266⟩, ⟨(-433453016856936390), (-425892405737041276)⟩, true⟩

def words03 : List Nat := [371285117637137273, 371285117628517645, 371285117656563539, 371285117659719981, 371285117550405552, 371285117422454765, 371285117293245485, 371285117287581659, 371285117271656764, 371285117327380554]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 90430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 90400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484741515217333, 362484865359279737⟩, ⟨15227634178608576, 22790821426863886⟩, true⟩

def words04 : List Nat := [371285117380196486, 371285117383374471, 371285117374728117, 371285117426693621, 371285117514511542, 371285117517669544, 371285117463887588, 371285117384029675, 371285117327127667, 371285117330771466]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 90440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 90400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk904A
