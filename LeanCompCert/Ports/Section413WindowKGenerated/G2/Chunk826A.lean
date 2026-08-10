import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk826A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584353542874192, 360584398093110603⟩, ⟨(-170283237216706489), (-167798044537933673)⟩, true⟩

def state01 : KState := ⟨⟨360604623232517963, 360604667793926488⟩, ⟨(-1844668310787595196), (-1842182195236462874)⟩, true⟩

def words00 : List Nat := [360582366836467983, 360582367103824580, 360582367370595227, 360582367637583455, 360582367779800608, 360582367812549775, 360582367840935892, 360582367869652435, 360582368044535423, 360582368315706440]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360606159191403822, 360606203764098935⟩, ⟨(-1971569558646435079), (-1969082510657892373)⟩, true⟩

def words01 : List Nat := [360582368494341250, 360582368673093430, 360582368998116043, 360582369434824166, 360582369757485940, 360582370080329012, 360582370329515309, 360582370472690736, 360582370762116933, 360582371051947571]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589416457232845, 360589461041093214⟩, ⟨(-588299016287566018), (-585811045770088842)⟩, true⟩

def words02 : List Nat := [360582371215768928, 360582371264862738, 360582371265918030, 360582371241513236, 360582371216916981, 360582371175616831, 360582371298598870, 360582371421831136, 360582371471359501, 360582371558383698]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360602311691935522, 360602356286972449⟩, ⟨(-1653909987421750888), (-1651421093328752594)⟩, true⟩

def words03 : List Nat := [360582371709794836, 360582371861557001, 360582372159381803, 360582372350465467, 360582372402093851, 360582372453794333, 360582372554218806, 360582372728677424, 360582372971451107, 360582373214486289]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592791622989682, 360592836229323517⟩, ⟨(-867185725985398285), (-864695898262341039)⟩, true⟩

def words04 : List Nat := [360582373358848037, 360582373506515978, 360582373674499889, 360582373842821401, 360582373974037692, 360582374058605421, 360582374069632888, 360582374080778485, 360582374087636423, 360582374215575803]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk826A
