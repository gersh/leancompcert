import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk912A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485467225571155, 362485593212288661⟩, ⟨(-52137111259131682), (-44379315897299682)⟩, true⟩

def state01 : KState := ⟨⟨362474216487578337, 362474342502705438⟩, ⟨973972746428443993, 981733132893160891⟩, true⟩

def words00 : List Nat := [371285106671354342, 371285106674542526, 371285106607706661, 371285106510406805, 371285106411926637, 371285106303022757, 371285106132564302, 371285106068888785, 371285106004093488, 371285105940189192]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 91200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 91200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486382500645625, 362486508544505272⟩, ⟨(-135730680134798242), (-127967672825373078)⟩, true⟩

def words01 : List Nat := [371285105824343865, 371285105825667714, 371285105926502539, 371285105929689465, 371285105888684188, 371285105829035627, 371285105768087467, 371285105749569568, 371285105694289715, 371285105713218339]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 91210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 91200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474935490434976, 362475061563041657⟩, ⟨908482591512573930, 916248221273017276⟩, true⟩

def words02 : List Nat := [371285105729125440, 371285105732320804, 371285105625228430, 371285105581442076, 371285105535951859, 371285105503550271, 371285105310239572, 371285105114059013, 371285104916614309, 371285104840705507]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 91220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 91200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479567656361495, 362479693757734510⟩, ⟨485882548144551784, 493650802404604884⟩, true⟩

def words03 : List Nat := [371285104732818164, 371285104676343502, 371285104618775331, 371285104565329300, 371285104452526612, 371285104369439060, 371285104317908305, 371285104321159003, 371285104278159263, 371285104222469326]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 91230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 91200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489041154849236, 362489167284736654⟩, ⟨(-378505363004559930), (-370734506945226872)⟩, true⟩

def words04 : List Nat := [371285104192534238, 371285104196081768, 371285104262335980, 371285104357822186, 371285104413542816, 371285104416731472, 371285104331891603, 371285104328949168, 371285104437520563, 371285104485348755]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 91240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 91200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk912A
