import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk950A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360597121930177919, 360597181503186204⟩, ⟨(-1431403417335614952), (-1427581864012166164)⟩, true⟩

def state01 : KState := ⟨⟨360593487459399074, 360593547045513348⟩, ⟨(-1086207510188073100), (-1082384711732319080)⟩, true⟩

def words00 : List Nat := [360582154587599914, 360582154588976578, 360582154685074337, 360582154789518323, 360582154865402535, 360582154866779452, 360582154864923015, 360582154780191138, 360582154719853324, 360582154841329282]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 95000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 95000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360571933137973214, 360571992737072084⟩, ⟨961747380115252431, 965571412301728823⟩, true⟩

def words01 : List Nat := [360582154955406172, 360582155069724956, 360582155095543110, 360582155096919905, 360582155012254739, 360582154881505130, 360582154750358200, 360582154652357974, 360582154612874357, 360582154507355201]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 95010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 95000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593899673082905, 360593959285174429⟩, ⟨(-1125597399779400611), (-1121772132967365111)⟩, true⟩

def words02 : List Nat := [360582154405322618, 360582154466850308, 360582154617058390, 360582154767527413, 360582154815414624, 360582154816791589, 360582154801070799, 360582154849532648, 360582154883727419, 360582155009380558]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 95020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 95000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590168845954497, 360590228471187033⟩, ⟨(-771034052574909291), (-767207536908216547)⟩, true⟩

def words03 : List Nat := [360582155079577520, 360582155149936042, 360582155269274812, 360582155455026249, 360582155598536854, 360582155742271242, 360582155824585142, 360582155913643125, 360582155999714100, 360582156086248868]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 95030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 95000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586223330090497, 360586282968281213⟩, ⟨(-396049866068660043), (-392222118791109789)⟩, true⟩

def words04 : List Nat := [360582156255375232, 360582156314418485, 360582156315651069, 360582156305416472, 360582156294957199, 360582156301662789, 360582156385251129, 360582156469099026, 360582156484804247, 360582156529645206]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 95040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 95000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk950A
