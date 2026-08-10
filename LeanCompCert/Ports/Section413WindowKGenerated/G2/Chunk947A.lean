import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk947A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360606629098367192, 360606688281179152⟩, ⟨(-2330797412932196595), (-2327012869725340323)⟩, true⟩

def state01 : KState := ⟨⟨360585480111591812, 360585539307488677⟩, ⟨(-328016536769940488), (-324230754360375464)⟩, true⟩

def words00 : List Nat := [360582116275774466, 360582116369511063, 360582116439615061, 360582116510101182, 360582116511256134, 360582116502804769, 360582116383108079, 360582116185525464, 360582115987683974, 360582115937929066]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 94700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 94700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574010708134995, 360574069916942935⟩, ⟨758356696300444367, 762143701583394325⟩, true⟩

def words01 : List Nat := [360582116053239765, 360582116168810947, 360582116221337321, 360582116283479549, 360582116292668271, 360582116302234060, 360582116307491663, 360582116308870651, 360582116281103564, 360582116197576206]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 94710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 94700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589370141346218, 360589429363097639⟩, ⟨(-696583704328064345), (-692795472972971143)⟩, true⟩

def words02 : List Nat := [360582116113746061, 360582116022151782, 360582116059369976, 360582116134529818, 360582116135808893, 360582116115290810, 360582115983442888, 360582115963406537, 360582115992385297, 360582116071007690]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 94720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 94700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360597145998350584, 360597205233193720⟩, ⟨(-1433276369486539313), (-1429486897889827467)⟩, true⟩

def words03 : List Nat := [360582116072257673, 360582116057455781, 360582116105442437, 360582116237854065, 360582116341648224, 360582116445665387, 360582116478219231, 360582116545838092, 360582116706211803, 360582116867038731]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 94730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 94700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590152377199737, 360590211624963248⟩, ⟨(-770714762766628719), (-766924067028990261)⟩, true⟩

def words04 : List Nat := [360582117065293322, 360582117178262589, 360582117198339183, 360582117218549682, 360582117219718497, 360582117163923949, 360582117272573737, 360582117383390255, 360582117438136205, 360582117524985106]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 94740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 94700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk947A
