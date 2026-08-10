import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk387A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360617527137502132, 360617536338033913⟩, ⟨(-1368348834928895252), (-1368108164924916964)⟩, true⟩

def state01 : KState := ⟨⟨360612205258714220, 360612214464179380⟩, ⟨(-1162490014844457697), (-1162249153894388397)⟩, true⟩

def words00 : List Nat := [360582186672914049, 360582187358576301, 360582187463365106, 360582187568197039, 360582187568634869, 360582187775263486, 360582188710661290, 360582189646110934, 360582189944023804, 360582190720181695]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 38700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 38700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360662089379721101, 360662098590122033⟩, ⟨(-3093708276401893136), (-3093467224363008934)⟩, true⟩

def words01 : List Nat := [360582192161654760, 360582193603206573, 360582195709979616, 360582197626718285, 360582198954933655, 360582200283120945, 360582201594503444, 360582203260648836, 360582205324484764, 360582207388335845]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 38710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 38700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360684489281351385, 360684498496732147⟩, ⟨(-3961353811959813964), (-3961112567076909082)⟩, true⟩

def words02 : List Nat := [360582209118087986, 360582210564458069, 360582212675681988, 360582214786960019, 360582216722648923, 360582218566441804, 360582219972486954, 360582221378510387, 360582223449219043, 360582226090466445]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 38720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 38700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360636804876573780, 360636814096889291⟩, ⟨(-2114381943647649629), (-2114140507617114195)⟩, true⟩

def words03 : List Nat := [360582228383148365, 360582230675802689, 360582232634676940, 360582234100986627, 360582235274501185, 360582236448098890, 360582238286125161, 360582240139203611, 360582241548393970, 360582242957589400]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 38730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 38700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360675239765078077, 360675248990334396⟩, ⟨(-3603622251117707725), (-3603380623656297227)⟩, true⟩

def words04 : List Nat := [360582244654157982, 360582246872225663, 360582249018700083, 360582251165163058, 360582252634494062, 360582253442162537, 360582254914051739, 360582256386018328, 360582258522084067, 360582260922319215]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 38740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 38700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk387A
