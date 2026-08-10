import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk572A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk572B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk572A

def state06 : KState := ⟨⟨360605067912772074, 360605088708830142⟩, ⟨(-1326481595849117906), (-1325677085106366046)⟩, true⟩

def words05 : List Nat := [360581936013891081, 360581936398086276, 360581936773521140, 360581936844926614, 360581936845667641, 360581936608354935, 360581936370895971, 360581936415388013, 360581936820369729, 360581937225532499]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 57250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 57200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360607467073101328, 360607487876758734⟩, ⟨(-1464056758880148244), (-1463251812962651200)⟩, true⟩

def words06 : List Nat := [360581937476952358, 360581937477750791, 360581937611819954, 360581937799511274, 360581937818568962, 360581937928391720, 360581937929122898, 360581937790781497, 360581937817998630, 360581938265036176]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 57260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 57200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585375230735126, 360585396041912331⟩, ⟨(-198637028741769020), (-197831652127727396)⟩, true⟩

def words07 : List Nat := [360581939016618102, 360581939768326791, 360581940310699247, 360581940860469901, 360581941252428462, 360581941644592535, 360581941973240753, 360581942215200209, 360581942276209071, 360581942337330922]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 57270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 57200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360617478099672879, 360617498918398284⟩, ⟨(-2037714265558014460), (-2036908456546198296)⟩, true⟩

def words08 : List Nat := [360581942369104919, 360581942553085742, 360581943041559943, 360581943530170128, 360581943758330980, 360581943759129751, 360581943911671455, 360581944140865875, 360581944572019508, 360581945193440679]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 57280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 57200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579013073535346, 360579033899863154⟩, ⟨166168085078364601, 166974329669733995⟩, true⟩

def words09 : List Nat := [360581945625870673, 360581946058369403, 360581946500193593, 360581947095455203, 360581947484526296, 360581947873702650, 360581948081835092, 360581948082634059, 360581947986974675, 360581947937030166]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 57290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 57200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 57200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk572B
