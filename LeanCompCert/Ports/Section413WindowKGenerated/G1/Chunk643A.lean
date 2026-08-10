import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk643A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476155306671527, 362476216259015651⟩, ⟨594743052861456742, 597390217655647250⟩, true⟩

def state01 : KState := ⟨⟨362499360354191442, 362499421326122760⟩, ⟨(-897381812731119755), (-894733388379327545)⟩, true⟩

def words00 : List Nat := [371285506885607459, 371285506897204271, 371285507149774978, 371285507403255802, 371285507613957551, 371285507651739312, 371285507902442104, 371285508154250014, 371285508504881758, 371285508723482787]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 64300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 64300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362499061031269605, 362499122023157319⟩, ⟨(-878115154322403223), (-875465446476433233)⟩, true⟩

def words01 : List Nat := [371285508906046946, 371285509089350619, 371285509487102975, 371285509768057238, 371285510108390423, 371285510449568239, 371285510743166346, 371285510745353892, 371285510928273771, 371285511142628776]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 64310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 64300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362497680194462547, 362497741205862254⟩, ⟨(-789279519706958905), (-786628556749382857)⟩, true⟩

def words02 : List Nat := [371285511575693104, 371285511748492831, 371285511872149794, 371285511996488410, 371285512181296913, 371285512256173140, 371285512571861948, 371285512888473764, 371285513183089421, 371285513375473338]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 64320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 64300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362508981203166119, 362509042234306667⟩, ⟨(-1516285188638116120), (-1513632955648675816)⟩, true⟩

def words03 : List Nat := [371285513741707623, 371285514109062324, 371285514716970411, 371285515076607580, 371285515398518472, 371285515721128980, 371285516084912321, 371285516329200400, 371285516696344859, 371285517064420457]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 64330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 64300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493435685231148, 362493496736140992⟩, ⟨(-516071889703315272), (-513418384659880142)⟩, true⟩

def words04 : List Nat := [371285517431744744, 371285517514973323, 371285517755092912, 371285517996402768, 371285518256921249, 371285518259109711, 371285518197859050, 371285518129136737, 371285518203913419, 371285518330449397]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 64340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 64300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk643A
