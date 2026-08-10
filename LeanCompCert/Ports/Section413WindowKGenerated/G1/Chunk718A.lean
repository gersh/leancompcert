import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk718A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362468903919343180, 362468980578497806⟩, ⟨1164568111991102984, 1168285289246812486⟩, true⟩

def state01 : KState := ⟨⟨362492551447246056, 362492628128459796⟩, ⟨(-533438485767899675), (-529719724559162217)⟩, true⟩

def words00 : List Nat := [371285251736412931, 371285251655578848, 371285251477011112, 371285251457592422, 371285251437427480, 371285251386266147, 371285251218571542, 371285251233746833, 371285251441261055, 371285251546535590]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 71800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 71800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482786039554603, 362482862743236480⟩, ⟨167890364645800188, 171610739400550220⟩, true⟩

def words01 : List Nat := [371285251641870927, 371285251738008067, 371285251914387746, 371285251994652251, 371285252121337738, 371285252248985708, 371285252358671660, 371285252361135441, 371285252229524393, 371285252199368485]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 71810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 71800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362469241177823781, 362469317903432812⟩, ⟨1140778038213381379, 1144499987892375331⟩, true⟩

def words02 : List Nat := [371285252328125150, 371285252330588923, 371285252234558643, 371285252132481403, 371285252029445844, 371285251939056038, 371285251750587028, 371285251626414274, 371285251501455541, 371285251357252837]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 71820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 71800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362497977596223000, 362498054344120289⟩, ⟨(-923495827812044030), (-919772277055470718)⟩, true⟩

def words03 : List Nat := [371285251137105789, 371285251099065874, 371285251164129800, 371285251166637658, 371285251114593396, 371285251031819669, 371285251056187805, 371285251095204783, 371285251275098913, 371285251456116845]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 71830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 71800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489253505090515, 362489330275226487⟩, ⟨(-296767945081699185), (-293042796581723833)⟩, true⟩

def words04 : List Nat := [371285251573594581, 371285251576065660, 371285251605044548, 371285251718375316, 371285251889292151, 371285251891756660, 371285251804746514, 371285251718814325, 371285251736621127, 371285251796199310]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 71840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 71800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk718A
