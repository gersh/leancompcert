import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk928A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk928B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk928A

def state06 : KState := ⟨⟨360576087778397105, 360576144596974111⟩, ⟨540985827993962340, 544548645904347880⟩, true⟩

def words05 : List Nat := [360582008581527989, 360582008729380540, 360582008807550803, 360582008846416899, 360582008847560990, 360582008805660814, 360582008835874480, 360582008847128664, 360582008848331129, 360582008786570325]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 92850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 92800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360607050465692160, 360607107296962287⟩, ⟨(-2334308696900968972), (-2330744700246520516)⟩, true⟩

def words06 : List Nat := [360582008777238783, 360582008947342953, 360582009232877563, 360582009518663571, 360582009695917733, 360582009796520699, 360582010012733836, 360582010229337266, 360582010442978321, 360582010714603462]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 92860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 92800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360596873716284884, 360596930560366404⟩, ⟨(-1389155269625031003), (-1385590083115507923)⟩, true⟩

def words07 : List Nat := [360582010903406854, 360582011092348041, 360582011298686662, 360582011578533845, 360582011827162091, 360582012076027455, 360582012260683409, 360582012329895621, 360582012491600075, 360582012653764241]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 92870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 92800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594775319716788, 360594832176468757⟩, ⟨(-1194291510610589797), (-1190725147205142295)⟩, true⟩

def words08 : List Nat := [360582012915100789, 360582013061107947, 360582013117749094, 360582013174523940, 360582013175653838, 360582013221488138, 360582013339060589, 360582013456890843, 360582013516993160, 360582013656405402]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 92880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 92800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602711888923836, 360602768758356362⟩, ⟨(-1931587129147521928), (-1928019587781465182)⟩, true⟩

def words09 : List Nat := [360582013846039030, 360582014036061041, 360582014341483160, 360582014531592548, 360582014605549937, 360582014679601891, 360582014714124489, 360582014823242693, 360582015047729911, 360582015272518950]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 92890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 92800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 92800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk928B
