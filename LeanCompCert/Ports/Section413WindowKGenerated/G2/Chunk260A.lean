import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk260A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360623682851490662, 360623686867346358⟩, ⟨(-1054016206764284263), (-1053945577219695421)⟩, true⟩

def state01 : KState := ⟨⟨360578535937479850, 360578539956581662⟩, ⟨119711946147081385, 119782660106678443⟩, true⟩

def words00 : List Nat := [360583152832227244, 360583152832568045, 360583152908834162, 360583153685261161, 360583153685551503, 360583153446396106, 360583151733491308, 360583149272403116, 360583146811439446, 360583145210718790]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 26000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 26000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360453146744150068, 360453150766467306⟩, ⟨3381795020713919290, 3381865818322812528⟩, true⟩

def words01 : List Nat := [360583145037933211, 360583145042267625, 360583145042573607, 360583143850559476, 360583141185531874, 360583137406072088, 360583133626803456, 360583131322403942, 360583127545326713, 360583122550415147]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 26010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 26000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602544742430051, 360602548767967512⟩, ⟨(-506332684567779481), (-506261803153085693)⟩, true⟩

def words02 : List Nat := [360583117555810755, 360583114035863528, 360583111258057265, 360583109471137120, 360583107684328151, 360583104602177875, 360583102623290824, 360583101124900566, 360583099626522301, 360583100348653883]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 26020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 26000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360538257947614553, 360538261976404491⟩, ⟨1167402080974159034, 1167473047066916568⟩, true⟩

def words03 : List Nat := [360583100349705275, 360583100350793692, 360583100351074549, 360583101008358043, 360583101008643931, 360583100945899749, 360583100883127638, 360583099670455376, 360583097532177244, 360583095810777261]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 26030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 26000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360528575359287180, 360528579391289471⟩, ⟨1419674821159336023, 1419745870918257771⟩, true⟩

def words04 : List Nat := [360583094089390161, 360583093839921922, 360583092847090613, 360583091109283885, 360583089371554298, 360583087254964888, 360583085897865076, 360583084293379891, 360583082688979075, 360583080192476353]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 26040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 26000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk260A
