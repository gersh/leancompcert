import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk806A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569166153448870, 360569208491584134⟩, ⟨1039935666054082636, 1042240341701127726⟩, true⟩

def state01 : KState := ⟨⟨360560893199274148, 360560935548379725⟩, ⟨1706673156420075160, 1708978716328849588⟩, true⟩

def words00 : List Nat := [360582139353788605, 360582139101788169, 360582138730262447, 360582138512791962, 360582138295026653, 360582137965295833, 360582137546240138, 360582137033594828, 360582136520733573, 360582136127914881]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 80600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 80600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360538197713682184, 360538240073667254⟩, ⟨3536362881836321007, 3538669318795189541⟩, true⟩

def words01 : List Nat := [360582135865848789, 360582135757698092, 360582135649419211, 360582135437268525, 360582135173742738, 360582134829060002, 360582134484049209, 360582134207660453, 360582133811153850, 360582133267896915]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 80610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 80600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591319414995296, 360591361785868636⟩, ⟨(-746612642981246176), (-744305328156280710)⟩, true⟩

def words02 : List Nat := [360582132724390861, 360582132334880754, 360582132022868950, 360582131800261469, 360582131577571671, 360582131220556531, 360582130927737442, 360582130788872258, 360582130663146306, 360582130778834663]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 80620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 80600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577900137386111, 360577942519269266⟩, ⟨335435899207290645, 337744101808909979⟩, true⟩

def words03 : List Nat := [360582130783617797, 360582130788513296, 360582130789462291, 360582130880215800, 360582130932413353, 360582130984800312, 360582130985828351, 360582130961383481, 360582130864769807, 360582130814182571]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 80630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 80600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360558303363320136, 360558345756058204⟩, ⟨1915804185003269308, 1918113263000500426⟩, true⟩

def words04 : List Nat := [360582130763184169, 360582130735990075, 360582130600783358, 360582130388904186, 360582130176842114, 360582129915024828, 360582129729842471, 360582129498114035, 360582129266274036, 360582128933528762]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 80640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 80600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk806A
