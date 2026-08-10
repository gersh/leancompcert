import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk296A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360634602005743222, 360634607269305375⟩, ⟨(-1514390845339315940), (-1514285477292708392)⟩, true⟩

def state01 : KState := ⟨⟨360589175448109534, 360589180715415568⟩, ⟨(-169838383298926707), (-169732904416119583)⟩, true⟩

def words00 : List Nat := [360583451410236958, 360583451964979549, 360583452492006507, 360583453019106981, 360583453036485087, 360583453036877313, 360583452245189466, 360583450772725889, 360583449300287218, 360583448625840204]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 29600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 29600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569930577937690, 360569935848935826⟩, ⟨400339444614614342, 400445032839491702⟩, true⟩

def words01 : List Nat := [360583449956625246, 360583451287397863, 360583452051003181, 360583453162014597, 360583453986966479, 360583454811966251, 360583455609758989, 360583455718288427, 360583455718641604, 360583455262603601]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 29610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 29600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581945644375049, 360581950919076473⟩, ⟨44377339186950466, 44483037121950786⟩, true⟩

def words02 : List Nat := [360583454842460397, 360583455454106445, 360583456234908096, 360583457015737126, 360583457016099392, 360583456817304188, 360583455484874821, 360583454012362316, 360583452539830657, 360583452202813293]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 29620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 29600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360620352950038357, 360620358228484839⟩, ⟨(-1093945836296571969), (-1093840027377658211)⟩, true⟩

def words03 : List Nat := [360583452152504070, 360583451114984754, 360583450174738454, 360583451138446072, 360583451816864063, 360583452495300505, 360583452495653828, 360583452798134849, 360583454043575046, 360583455289063846]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 29630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 29600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596060139257008, 360596065421399428⟩, ⟨(-373827696958588705), (-373721778473571757)⟩, true⟩

def words04 : List Nat := [360583457668710115, 360583458915660638, 360583459430929888, 360583459946207022, 360583459946543755, 360583459565509544, 360583460224241069, 360583460883003757, 360583460976524686, 360583461402024919]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 29640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 29600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk296A
