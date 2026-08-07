import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk874

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

def state06 : KState := ⟨⟨360552172666252954, 360552222834762411⟩, ⟨2614001312989317266, 2616964366640486268⟩, true⟩

def words05 : List Nat := [360582147010640252, 360582146885492960, 360582146760223373, 360582146549949705, 360582146245984810, 360582145909569534, 360582145572794256, 360582145293900487, 360582145018330117, 360582144677509273]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 87450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 87400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360565420356471323, 360565470536863554⟩, ⟨1455292434662697564, 1458256527637838360⟩, true⟩

def words06 : List Nat := [360582144336417416, 360582144016118368, 360582143771581818, 360582143628895597, 360582143486131467, 360582143207428291, 360582142833616031, 360582142549186304, 360582142264393876, 360582142041695358]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 87460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 87400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360558843675332870, 360558893867743108⟩, ⟨2030635395053038045, 2033600539300649873⟩, true⟩

def words07 : List Nat := [360582141852232950, 360582141597684522, 360582141342869703, 360582141218931547, 360582141174299992, 360582141095901463, 360582141017369987, 360582140856004976, 360582140594526908, 360582140330240830]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 87470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 87400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360577183648900425, 360577233853166184⟩, ⟨426157337730910327, 429123519159644409⟩, true⟩

def words08 : List Nat := [360582140065527042, 360582139931544446, 360582139803763001, 360582139576051425, 360582139348139521, 360582139087834024, 360582138928125308, 360582138868006454, 360582138807762061, 360582138682508505]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 87480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 87400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360595838342660237, 360595888558830799⟩, ⟨(-1206043021572457516), (-1203075798534351626)⟩, true⟩

def words09 : List Nat := [360582138701852541, 360582138777627938, 360582138809925141, 360582138879090672, 360582138880254663, 360582138840538976, 360582138847396637, 360582138961645983, 360582139119804997, 360582139278267899]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 87490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 87400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 87400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk874
