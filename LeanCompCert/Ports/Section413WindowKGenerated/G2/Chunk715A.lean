import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk715A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571551834858490, 360571584839411849⟩, ⟨766206812463419202, 767800762186323600⟩, true⟩

def state01 : KState := ⟨⟨360597467734635969, 360597500748749443⟩, ⟨(-1086862553675768551), (-1085267920356930279)⟩, true⟩

def words00 : List Nat := [360582323163758795, 360582323302635214, 360582323636492537, 360582323970535135, 360582324112295424, 360582324113309653, 360582324096456217, 360582324134276501, 360582324297967242, 360582324511242529]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 71500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 71500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568686450780338, 360568719474567489⟩, ⟨971488228500872305, 973083553631723341⟩, true⟩

def words01 : List Nat := [360582324578332244, 360582324645542058, 360582324770345515, 360582325022384772, 360582325224554500, 360582325426886035, 360582325519543723, 360582325520558104, 360582325418035383, 360582325228952721]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 71510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 71500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590048617694123, 360590081651034752⟩, ⟨(-556477837025637861), (-554881828582339213)⟩, true⟩

def words02 : List Nat := [360582325039539060, 360582324963252280, 360582324858575992, 360582324655009372, 360582324451284175, 360582324199022179, 360582324213209491, 360582324318477154, 360582324319791760, 360582324429290581]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 71520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 71500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360598058820256406, 360598091863189089⟩, ⟨(-1129532685452867343), (-1127935990842304069)⟩, true⟩

def words03 : List Nat := [360582324697116667, 360582324965243342, 360582325129818829, 360582325163971119, 360582325164909088, 360582325035008321, 360582324969096560, 360582325132785974, 360582325354000832, 360582325575454192]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 71530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 71500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582636648943459, 360582669701543179⟩, ⟨(-26292840273779462), (-24695454036843986)⟩, true⟩

def words04 : List Nat := [360582325698723287, 360582325699738080, 360582325662161296, 360582325697498436, 360582325698348282, 360582325637043752, 360582325430786022, 360582325072830527, 360582324714690044, 360582324556764814]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 71540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 71500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk715A
