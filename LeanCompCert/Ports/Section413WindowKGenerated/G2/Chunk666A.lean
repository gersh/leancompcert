import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk666A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598206130410857, 360598234605176600⟩, ⟨(-1021351887651166150), (-1020070861328944100)⟩, true⟩

def state01 : KState := ⟨⟨360592341478027413, 360592369961632308⟩, ⟨(-630757573403246964), (-629475958348401700)⟩, true⟩

def words00 : List Nat := [360582918911559313, 360582919142559267, 360582919248694146, 360582919354928272, 360582919355733775, 360582919307536824, 360582919505244261, 360582919703126768, 360582919788638199, 360582919931481907]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360609857736086105, 360609886228576224⟩, ⟨(-1797589755720418694), (-1796307548777161646)⟩, true⟩

def words01 : List Nat := [360582920227727303, 360582920524262503, 360582920942386748, 360582921262073127, 360582921389403640, 360582921516809785, 360582921868889302, 360582922334414915, 360582922739930371, 360582923145632751]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597757379981086, 360597785881417300⟩, ⟨(-991575874022659020), (-990293071045320674)⟩, true⟩

def words02 : List Nat := [360582923419481224, 360582923468683781, 360582923594432542, 360582923720451192, 360582923721242902, 360582923690527879, 360582923666014121, 360582923472734337, 360582923309865860, 360582923533995750]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578389003500756, 360578417513807811⟩, ⟨299029371618434415, 300312765703304615⟩, true⟩

def words03 : List Nat := [360582923864562605, 360582924195298462, 360582924342816764, 360582924343756852, 360582924266534385, 360582924133222054, 360582923999627792, 360582924073685655, 360582924074523410, 360582924007890994]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597603607495216, 360597632126666519⟩, ⟨(-981447131489766870), (-980163146647316950)⟩, true⟩

def words04 : List Nat := [360582924046724134, 360582924294475414, 360582924766623839, 360582925238938143, 360582925518872951, 360582925649320167, 360582925774834343, 360582925900607359, 360582926001960319, 360582926223579584]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk666A
