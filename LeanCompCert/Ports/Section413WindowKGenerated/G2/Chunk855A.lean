import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk855A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360561886286106380, 360561934147434846⟩, ⟨1744849649921432642, 1747613169440156668⟩, true⟩

def state01 : KState := ⟨⟨360549953557152738, 360550001430045482⟩, ⟨2765087703645509598, 2767852211969923662⟩, true⟩

def words00 : List Nat := [360582373829482767, 360582373632446529, 360582373298488018, 360582372860450585, 360582372422241079, 360582371885984415, 360582371418243692, 360582371030327555, 360582370642297685, 360582370184717099]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 85500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 85500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360581608468444831, 360581656352956477⟩, ⟨58160103934467289, 60925605849094723⟩, true⟩

def words01 : List Nat := [360582369807177323, 360582369542667816, 360582369277779930, 360582369149778221, 360582369099050960, 360582368932246403, 360582368765210160, 360582368772540374, 360582368773553433, 360582368766495405]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 85510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 85500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580345357738381, 360580393253951947⟩, ⟨166100787998730635, 168867290719544665⟩, true⟩

def words02 : List Nat := [360582368759261116, 360582368667274745, 360582368480501886, 360582368430704160, 360582368380589812, 360582368239161422, 360582368147888948, 360582367951062912, 360582367754006700, 360582367617224712]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 85520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 85500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360563044265146740, 360563092172957477⟩, ⟨1645993459044872484, 1648760953729447010⟩, true⟩

def words03 : List Nat := [360582367708638992, 360582367823369885, 360582367833401413, 360582367834630742, 360582367707868894, 360582367547035952, 360582367385823736, 360582367289045086, 360582367133412998, 360582366909381717]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 85530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 85500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360578560905454993, 360578608824858542⟩, ⟨318643718691656386, 321412205082245970⟩, true⟩

def words04 : List Nat := [360582366685048040, 360582366572899053, 360582366615631955, 360582366692751368, 360582366693895844, 360582366654247823, 360582366477715086, 360582366218061791, 360582365958053383, 360582365834853659]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 85540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 85500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk855A
