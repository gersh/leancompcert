import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk712A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk712B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk712A

def state06 : KState := ⟨⟨362470749386863328, 362470824852903360⟩, ⟨1023575597415047551, 1027207430626307591⟩, true⟩

def words05 : List Nat := [371285241292094182, 371285241229575274, 371285241166316789, 371285241063158465, 371285240747012000, 371285240491913462, 371285240235534714, 371285240176587491, 371285239975672034, 371285239776150993]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478146663572698, 362478222151465846⟩, ⟨496500872839761013, 500134263416504849⟩, true⟩

def words06 : List Nat := [371285239575524380, 371285239572561733, 371285239582202431, 371285239687181086, 371285239759656060, 371285239762110242, 371285239646187206, 371285239613913859, 371285239607382911, 371285239609911427]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481207423926925, 362481282934129478⟩, ⟨278380844517448386, 282015825191298398⟩, true⟩

def words07 : List Nat := [371285239513293192, 371285239417012245, 371285239400064812, 371285239412625180, 371285239485933886, 371285239560152218, 371285239618802752, 371285239621245818, 371285239437493847, 371285239385100176]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469629356980163, 362469704888940545⟩, ⟨1103709015472660856, 1107345547157492666⟩, true⟩

def words08 : List Nat := [371285239331286071, 371285239307740351, 371285239069712062, 371285238832905703, 371285238595192577, 371285238404422051, 371285238121740997, 371285238036609475, 371285237950598205, 371285237860565703]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483139204170525, 362483214758198796⟩, ⟨140529898423418746, 144168003437110728⟩, true⟩

def words09 : List Nat := [371285237644353197, 371285237531344151, 371285237497614252, 371285237500058702, 371285237352481223, 371285237140173157, 371285236926841736, 371285236892705052, 371285236775459752, 371285236749831856]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk712B
