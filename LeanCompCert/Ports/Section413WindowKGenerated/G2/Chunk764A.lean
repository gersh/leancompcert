import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk764A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585137977742716, 360585175859218858⟩, ⟨(-230703178068449192), (-228748438711461906)⟩, true⟩

def state01 : KState := ⟨⟨360583877755041939, 360583915646893963⟩, ⟨(-134549646536853972), (-132594114411863106)⟩, true⟩

def words00 : List Nat := [360582181809880221, 360582181743319020, 360582181505628486, 360582181439315906, 360582181372733118, 360582181153050606, 360582180981301381, 360582180724030946, 360582180466558749, 360582180371679507]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 76400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 76400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360557603911548068, 360557641813673807⟩, ⟨1873235407242215750, 1875191724434238982⟩, true⟩

def words01 : List Nat := [360582180505721778, 360582180639987776, 360582180688501690, 360582180689596171, 360582180687165694, 360582180546618607, 360582180405761549, 360582180291777199, 360582180104390175, 360582179784420134]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 76410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 76400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597258966535582, 360597296878943725⟩, ⟨(-1157353938653200226), (-1155396835629445360)⟩, true⟩

def words02 : List Nat := [360582179464211600, 360582179315281487, 360582179387398358, 360582179509576536, 360582179510582583, 360582179510625685, 360582179586745095, 360582179663197416, 360582179818603144, 360582180017518002]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 76420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 76400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360570539297382769, 360570577220183926⟩, ⟨884982244128164347, 886940141540227449⟩, true⟩

def words03 : List Nat := [360582180119526702, 360582180221654361, 360582180284116261, 360582180432608806, 360582180537825264, 360582180643216726, 360582180644199766, 360582180637556387, 360582180459948956, 360582180309424380]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 76430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 76400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569571083894638, 360569609016951422⟩, ⟨959003037012456767, 960961718415328239⟩, true⟩

def words04 : List Nat := [360582180177586841, 360582180178677121, 360582180100635989, 360582179928572274, 360582179756334480, 360582179541449154, 360582179427644661, 360582179266090362, 360582179104424196, 360582178823601721]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 76440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 76400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk764A
