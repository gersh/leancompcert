import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk736A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360542194929662122, 360542229981924638⟩, ⟨2956309906960581993, 2958052429011407973⟩, true⟩

def state01 : KState := ⟨⟨360588660712342161, 360588695774482118⟩, ⟨(-463873848789132712), (-462130599710444654)⟩, true⟩

def words00 : List Nat := [360582420366453350, 360582419850117214, 360582419455103911, 360582419199579291, 360582418943997331, 360582418515303232, 360582418121840784, 360582417912964515, 360582417703786955, 360582417764406037]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 73600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 73600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360571843225935421, 360571878298060030⟩, ⟨774230075345073646, 775974059444134822⟩, true⟩

def words01 : List Nat := [360582417765347253, 360582417758458136, 360582417927631433, 360582418197994664, 360582418421393115, 360582418644956519, 360582418764939927, 360582418765986463, 360582418701634362, 360582418559666172]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 73610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 73600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360560487859448438, 360560522941429043⟩, ⟨1610244503337686643, 1611989213083075885⟩, true⟩

def words02 : List Nat := [360582418417343293, 360582418418150352, 360582418276866303, 360582417969335656, 360582417661646442, 360582417252044840, 360582416982726920, 360582416705065567, 360582416427307423, 360582416044961341]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 73620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 73600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360581789017566815, 360581824109442382⟩, ⟨41661462481223142, 43406900842183328⟩, true⟩

def words03 : List Nat := [360582415748473100, 360582415551802773, 360582415354839940, 360582415107082789, 360582414832480943, 360582414400308771, 360582413967947519, 360582413720051877, 360582413563667014, 360582413556765063]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 73630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 73600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360566691014680997, 360566726116525960⟩, ⟨1153445703508161458, 1155191876063910662⟩, true⟩

def words04 : List Nat := [360582413549693690, 360582413450809749, 360582413167578032, 360582413068768983, 360582412969689904, 360582412707017251, 360582412358989943, 360582411865068509, 360582411370960374, 360582411002826896]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 73640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 73600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk736A
