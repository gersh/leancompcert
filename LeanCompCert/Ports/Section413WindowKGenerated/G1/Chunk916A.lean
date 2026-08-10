import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk916A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480243703994358, 362480370841181211⟩, ⟨425874679234334510, 433737627805880286⟩, true⟩

def state01 : KState := ⟨⟨362486643392941676, 362486770558802636⟩, ⟨(-160304479906546680), (-152438904639827372)⟩, true⟩

def words00 : List Nat := [371285105978586841, 371285105999806319, 371285106119780297, 371285106241025205, 371285106353873808, 371285106357075182, 371285106390216733, 371285106460488350, 371285106556965893, 371285106578443948]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 91600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 91600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484430650543691, 362484557845573064⟩, ⟨42430465139449000, 50298712671955620⟩, true⟩

def words01 : List Nat := [371285106592383799, 371285106607338768, 371285106694669158, 371285106723933292, 371285106782807740, 371285106843013923, 371285106901851004, 371285106905059615, 371285106840313937, 371285106838289414]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 91610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 91600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484776789688291, 362484904013264864⟩, ⟨10711375802033245, 18582238976331317⟩, true⟩

def words02 : List Nat := [371285106947545907, 371285106950748284, 371285106923790294, 371285106874830212, 371285106824601942, 371285106811056755, 371285106757868017, 371285106782426178, 371285106806311850, 371285106809717733]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 91620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 91600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493984654017776, 362494111906542671⟩, ⟨(-833036698157455864), (-825163182305514456)⟩, true⟩

def words03 : List Nat := [371285106926510696, 371285107047224629, 371285107264588734, 371285107324278971, 371285107351581608, 371285107379853366, 371285107420045900, 371285107423611506, 371285107503279571, 371285107605167681]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 91630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 91600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481762602813502, 362481889884231741⟩, ⟨287010602907205862, 294886766691244900⟩, true⟩

def words04 : List Nat := [371285107684022291, 371285107687224622, 371285107635579211, 371285107667854426, 371285107735006336, 371285107738208834, 371285107646878940, 371285107539152033, 371285107430078615, 371285107415783201]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 91640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 91600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk916A
