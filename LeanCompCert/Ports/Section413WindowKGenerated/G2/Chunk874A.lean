import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk874A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360549203692786514, 360549253789838650⟩, ⟨2872326649893324276, 2875283456033228634⟩, true⟩

def state01 : KState := ⟨⟨360584889902862390, 360584940011800029⟩, ⟨(-246784283019828247), (-243826438026140473)⟩, true⟩

def words00 : List Nat := [360582151394499097, 360582151113950902, 360582150934312983, 360582150885644650, 360582150836879678, 360582150676970620, 360582150550806340, 360582150553975386, 360582150555010199, 360582150586693051]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 87400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 87400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360575342105494794, 360575392226414634⟩, ⟨587877770106520040, 590836662522586146⟩, true⟩

def words01 : List Nat := [360582150587814030, 360582150555468025, 360582150580633015, 360582150731505150, 360582150849181302, 360582150967082490, 360582150985202328, 360582150986460792, 360582150900580191, 360582150824704758]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 87410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 87400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360577966973889877, 360578017106678457⟩, ⟨358348218918603110, 361308148960172584⟩, true⟩

def words02 : List Nat := [360582150801772571, 360582150803031026, 360582150726823241, 360582150544007930, 360582150360997727, 360582150103090448, 360582149909602834, 360582149847023407, 360582149784299637, 360582149648700191]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 87420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 87400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577136479860632, 360577186624524625⟩, ⟨430936957827092729, 433897926194038129⟩, true⟩

def words03 : List Nat := [360582149602454569, 360582149548022146, 360582149568048079, 360582149569306768, 360582149514619906, 360582149341593099, 360582149168346755, 360582148992195462, 360582148916090729, 360582148860643039]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 87430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 87400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577075539220157, 360577125695870139⟩, ⟨436156890438847993, 439118906918014057⟩, true⟩

def words04 : List Nat := [360582148805014928, 360582148684054009, 360582148432191357, 360582148311351199, 360582148190142467, 360582148036329352, 360582147821904050, 360582147535832391, 360582147249522534, 360582147067018430]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 87440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 87400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk874A
