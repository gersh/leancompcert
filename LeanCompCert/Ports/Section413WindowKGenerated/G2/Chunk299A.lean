import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk299A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360609879052525428, 360609884428035494⟩, ⟨(-790386187739549969), (-790277489220766695)⟩, true⟩

def state01 : KState := ⟨⟨360565650499787119, 360565655879070029⟩, ⟨532009051651563343, 532117862997576673⟩, true⟩

def words00 : List Nat := [360583454955535567, 360583454955932021, 360583454170973515, 360583453763583372, 360583453356108411, 360583452667473499, 360583451515415156, 360583449790723308, 360583448066073300, 360583446513071954]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 29900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 29900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360511264518249087, 360511269901272324⟩, ⟨2158879019112952858, 2158987942351197088⟩, true⟩

def words01 : List Nat := [360583445918612694, 360583445300619889, 360583444682627013, 360583443277233995, 360583440758939755, 360583437754071677, 360583434749284306, 360583432857551894, 360583431000572415, 360583428589185132]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 29910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 29900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360618685089816550, 360618690476581249⟩, ⟨(-1055731955238488410), (-1055622920037373786)⟩, true⟩

def words02 : List Nat := [360583426177865887, 360583424879316470, 360583424143484330, 360583423921329377, 360583423699169236, 360583422496408791, 360583420980108539, 360583420576075959, 360583420749473690, 360583421928252180]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 29920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 29900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360545839388802792, 360545844779350467⟩, ⟨1125068738118931056, 1125177886563488206⟩, true⟩

def words03 : List Nat := [360583422244916641, 360583422561607619, 360583423499613705, 360583424994041450, 360583426207633666, 360583427421209414, 360583427828895389, 360583427829292292, 360583427125889300, 360583425871086055]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 29930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 29900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583131202947951, 360583136597233006⟩, ⟨8359072981316691, 8468333341289815⟩, true⟩

def words04 : List Nat := [360583424616235717, 360583424158307270, 360583423548148370, 360583422386268453, 360583421224400846, 360583419608850155, 360583419282318754, 360583419674585264, 360583419674939150, 360583419346259427]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 29940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 29900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk299A
