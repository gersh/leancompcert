import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk345A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586403545116789, 360586410788508432⟩, ⟨(-166974180744992877), (-166805226876605241)⟩, true⟩

def state01 : KState := ⟨⟨360606127125946321, 360606134373696540⟩, ⟨(-847602024027537567), (-847432919767266669)⟩, true⟩

def words00 : List Nat := [360581576974123072, 360581577710370943, 360581577786851739, 360581577863372204, 360581577863758930, 360581577738705010, 360581578039159011, 360581578339681574, 360581578340093167, 360581578929931733]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 34500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 34500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360659130662406262, 360659137914514060⟩, ⟨(-2677054966498535003), (-2676885711836382639)⟩, true⟩

def words01 : List Nat := [360581580480384252, 360581582030882221, 360581584419680854, 360581585972471269, 360581586764483467, 360581587556480066, 360581588322333739, 360581589731158519, 360581591978003384, 360581594224822673]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 34510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 34500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592485067600504, 360592492324111579⟩, ⟨(-376285135306886305), (-376115728621970607)⟩, true⟩

def words02 : List Nat := [360581595922993081, 360581597161371159, 360581598305189500, 360581599449089135, 360581600368615293, 360581600724700481, 360581600725113382, 360581600506080305, 360581600286971912, 360581600206054704]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 34520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 34500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360564810085966887, 360564817346835061⟩, ⟨579432934604134629, 579602491761911249⟩, true⟩

def words03 : List Nat := [360581600496022841, 360581600786056388, 360581600786472483, 360581600647216567, 360581600038071675, 360581599216540697, 360581598410465506, 360581598448224125, 360581598448636446, 360581597963272870]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 34530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 34500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360640024296827273, 360640031562058753⟩, ⟨(-2018879192624960348), (-2018709484737274928)⟩, true⟩

def words04 : List Nat := [360581597477831331, 360581597536155838, 360581598679229775, 360581599822327369, 360581600185065701, 360581600185529006, 360581600811052537, 360581601448323583, 360581602922368529, 360581604613931716]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 34540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 34500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk345A
