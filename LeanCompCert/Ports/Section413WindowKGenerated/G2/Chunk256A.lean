import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk256A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360466786144787138, 360466790032745290⟩, ⟨2983813944049836768, 2983881273770723908⟩, true⟩

def state01 : KState := ⟨⟨360634460870915167, 360634464762036440⟩, ⟨(-1309498967201679127), (-1309431556489344037)⟩, true⟩

def words00 : List Nat := [360583343342409558, 360583340312093933, 360583338385850900, 360583337981526266, 360583337577209833, 360583335840523239, 360583334667977440, 360583334293131434, 360583335064050894, 360583337060795203]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360544954810821552, 360544958705138498⟩, ⟨983352204216180002, 983419696785371670⟩, true⟩

def words01 : List Nat := [360583338287310961, 360583339513768080, 360583340698303607, 360583342679274949, 360583344034966965, 360583345390607521, 360583345976806199, 360583345977141463, 360583345046792468, 360583343548885000]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360548595132519540, 360548599029992779⟩, ⟨890056809364871633, 890124382814057511⟩, true⟩

def words02 : List Nat := [360583342072521013, 360583342072856802, 360583341451466832, 360583339848604753, 360583338245813778, 360583335955677473, 360583334424123208, 360583332810336704, 360583331196639608, 360583328814729965]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360646533514407064, 360646537415044920⟩, ⟨(-1620735182912205801), (-1620667528337960679)⟩, true⟩

def words03 : List Nat := [360583327460010647, 360583326482050628, 360583326044098667, 360583326634507444, 360583326634816768, 360583325941502332, 360583325438958329, 360583326387149914, 360583328852750164, 360583331318233643]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567144329752448, 360567148233593675⟩, ⟨414885577715768466, 414953314439376972⟩, true⟩

def words04 : List Nat := [360583332274266723, 360583332274602222, 360583332676907553, 360583333636853534, 360583333706264278, 360583333706599833, 360583332262990722, 360583329949808174, 360583327636737623, 360583325750725815]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk256A
