import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk339A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360614826710235258, 360614833693672366⟩, ⟨(-1133220622290541617), (-1133060559105805161)⟩, true⟩

def state01 : KState := ⟨⟨360614432302078550, 360614439289790721⟩, ⟨(-1119908624174704165), (-1119748416043655759)⟩, true⟩

def words00 : List Nat := [360581411741965494, 360581412713017128, 360581413248648793, 360581413784296820, 360581414099019082, 360581414852656563, 360581416104323161, 360581417356010482, 360581418103357190, 360581419077586904]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 33900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 33900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360649190195683327, 360649197187677434⟩, ⟨(-2298764295406969666), (-2298603942054219506)⟩, true⟩

def words01 : List Nat := [360581420920354770, 360581422763151710, 360581424735076656, 360581426219736550, 360581426866810772, 360581427513873351, 360581428409156040, 360581429742574587, 360581431740802719, 360581433739015714]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 33910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 33900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360613723831008037, 360613730827334561⟩, ⟨(-1095587513120881134), (-1095427012791866894)⟩, true⟩

def words02 : List Nat := [360581435302847412, 360581436889008250, 360581439342995913, 360581441796974982, 360581443686464641, 360581444710490767, 360581445209387300, 360581445708303864, 360581445916323539, 360581446868335656]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 33920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 33900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360597427667590168, 360597434668190340⟩, ⟨(-542435294229356710), (-542274648873748558)⟩, true⟩

def words03 : List Nat := [360581448687871481, 360581450507388079, 360581451889457786, 360581453084641557, 360581453707189566, 360581454329826990, 360581455819768908, 360581456746663654, 360581457217841984, 360581457689053787]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 33930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 33900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360655467392261920, 360655474397156325⟩, ⟨(-2512649766832992208), (-2512488975710330540)⟩, true⟩

def words04 : List Nat := [360581459027464495, 360581460803167149, 360581462211012141, 360581463618852970, 360581464315416397, 360581464891223006, 360581466111009000, 360581467330861455, 360581468830382668, 360581471010637215]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 33940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 33900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk339A
