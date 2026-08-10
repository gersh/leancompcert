import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk487A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk487B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk487A

def state06 : KState := ⟨⟨360531018141592494, 360531033026287215⟩, ⟨2489413431094635177, 2489903857921243429⟩, true⟩

def words05 : List Nat := [360582102730421525, 360582102568089942, 360582102405692745, 360582102030107804, 360582101476718248, 360582100640336266, 360582099803789858, 360582099386605962, 360582098549041516, 360582097502454591]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 48750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 48700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360555071052301273, 360555085943342038⟩, ⟨1316532170114931193, 1317022906405360235⟩, true⟩

def words06 : List Nat := [360582096455757390, 360582095828455805, 360582095546736348, 360582095072246856, 360582094597724348, 360582093761686946, 360582092688794701, 360582092035203340, 360582091381451362, 360582090718950104]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 48760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 48700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360547687226503931, 360547702123946808⟩, ⟨1676622970863633580, 1677114019416240642⟩, true⟩

def words07 : List Nat := [360582090165848318, 360582089399879500, 360582088633816071, 360582087797311461, 360582087279711396, 360582086650675799, 360582086021577835, 360582085132442196, 360582084009219456, 360582083305156654]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 48770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 48700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360557065158548164, 360557080062326267⟩, ⟨1218999802437784881, 1219491160053948307⟩, true⟩

def words08 : List Nat := [360582082600892958, 360582082315653748, 360582081610457382, 360582080547671117, 360582079484822647, 360582078146452135, 360582077052610097, 360582076377725156, 360582075702803490, 360582074757141884]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 48780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 48700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586166677948161, 360586181588063417⟩, ⟨(-201046503699116209), (-200554836861244353)⟩, true⟩

def words09 : List Nat := [360582074245404358, 360582074036689845, 360582073896128956, 360582073896801491, 360582073721947613, 360582073186447020, 360582072650844579, 360582072106695256, 360582071857103332, 360582071942013926]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 48790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 48700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 48700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk487B
