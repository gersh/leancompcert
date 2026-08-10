import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk523A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk523B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk523A

def state06 : KState := ⟨⟨360550766487591851, 360550783751327771⟩, ⟨1637030775631118160, 1637641541620375656⟩, true⟩

def words05 : List Nat := [360582061776575357, 360582062224300511, 360582062390864957, 360582062391589922, 360582062194203039, 360582061829072569, 360582061463743658, 360582061310977750, 360582060924330908, 360582060327752912]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 52350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 52300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360586391456576915, 360586408727147882⟩, ⟨(-228408832181317402), (-227797708274013438)⟩, true⟩

def words06 : List Nat := [360582059731013303, 360582059498548559, 360582059758554241, 360582060070992352, 360582060071660957, 360582060072114067, 360582059708716291, 360582059335338474, 360582058961762239, 360582059035366667]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 52360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 52300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360581863817135824, 360581881094620915⟩, ⟨8718712593598280, 9330198625902956⟩, true⟩

def words07 : List Nat := [360582059036024011, 360582058816179356, 360582058653846705, 360582059037160814, 360582059314185300, 360582059591316888, 360582059591967856, 360582059589023997, 360582059222398391, 360582059219833323]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 52370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 52300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593219597767137, 360593236882090511⟩, ⟨(-586259301280089055), (-585647457023739849)⟩, true⟩

def words08 : List Nat := [360582059217029513, 360582059202741011, 360582059134195521, 360582058841301238, 360582058548299766, 360582058164261663, 360582058126145179, 360582058289378582, 360582058290030855, 360582058483949156]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 52380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 52300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360641908808247065, 360641926099414820⟩, ⟨(-3137367523599864024), (-3136755320732982074)⟩, true⟩

def words09 : List Nat := [360582059061553248, 360582059639348713, 360582060259116254, 360582060963229104, 360582061323681536, 360582061684165301, 360582062322706554, 360582063212892558, 360582064355900775, 360582065499030611]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 52390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 52300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 52300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk523B
