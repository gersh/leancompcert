import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk672A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578640943821104, 360578669954624844⟩, ⟨286499050650451605, 287815938165213415⟩, true⟩

def state01 : KState := ⟨⟨360562312612377315, 360562341632113217⟩, ⟨1383737405001703199, 1385054892801724899⟩, true⟩

def words00 : List Nat := [360582952866930659, 360582952785424365, 360582952482764961, 360582952037929897, 360582951592953182, 360582951092660083, 360582950731676368, 360582950365977844, 360582950000186385, 360582949501370794]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 67200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 67200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360619668697256335, 360619697725935441⟩, ⟨(-2471482689363343614), (-2470164600444462984)⟩, true⟩

def words01 : List Nat := [360582949195523335, 360582949110931174, 360582949161362808, 360582949303876270, 360582949304751232, 360582949258446048, 360582949385645280, 360582949712456634, 360582950259906499, 360582950807555107]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 67210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 67200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360596412747158102, 360596441784897199⟩, ⟨(-908181768701831248), (-906863070727696330)⟩, true⟩

def words02 : List Nat := [360582951131885685, 360582951473845452, 360582951880923940, 360582952288265117, 360582952638111784, 360582952767173935, 360582952785673881, 360582952804293617, 360582952819491135, 360582953021220805]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 67220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 67200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360562202754073295, 360562231800744843⟩, ⟨1392011619837525951, 1393330918384766573⟩, true⟩

def words03 : List Nat := [360582953443470291, 360582953865895410, 360582954164935605, 360582954243181753, 360582954243992130, 360582954125569540, 360582954045275692, 360582954046224879, 360582953864610978, 360582953557413267]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 67230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 67200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567999219944061, 360568028275587240⟩, ⟨1002280194662787923, 1003600096507983379⟩, true⟩

def words04 : List Nat := [360582953250010896, 360582953039752323, 360582952998976830, 360582952992496801, 360582952985943157, 360582952790931220, 360582952374898608, 360582952179905985, 360582951984648055, 360582951697096653]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 67240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 67200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk672A
