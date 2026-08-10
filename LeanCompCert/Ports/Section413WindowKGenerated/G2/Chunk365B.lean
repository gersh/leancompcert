import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk365A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk365B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk365A

def state06 : KState := ⟨⟨360623174977913873, 360623183150932952⟩, ⟨(-1513809874200178729), (-1513607880714970501)⟩, true⟩

def words05 : List Nat := [360581782133410748, 360581782055126162, 360581782005376139, 360581782080369862, 360581782080823170, 360581781522661606, 360581780978205372, 360581781364399811, 360581782497231520, 360581783630112544]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 36550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 36500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581783959274329, 360581792136984102⟩, ⟨(-484328835843444), (-282163836199320)⟩, true⟩

def words06 : List Nat := [360581784191343004, 360581784239365847, 360581785034004099, 360581785828746529, 360581786283422637, 360581786283914816, 360581786256752905, 360581785689534105, 360581785122245940, 360581784421476290]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 36560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 36500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360517252164769747, 360517260347109034⟩, ⟨2359921934768601556, 2360124269092605764⟩, true⟩

def words07 : List Nat := [360581785168581223, 360581785915739761, 360581786237839164, 360581786238331345, 360581785814548169, 360581784681864150, 360581783549093013, 360581782965770987, 360581781636658837, 360581779873328078]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 36570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 36500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595341677288121, 360595349864280019⟩, ⟨(-496855852585399101), (-496653348045905725)⟩, true⟩

def words08 : List Nat := [360581778109981927, 360581776911786443, 360581776576875118, 360581776782730991, 360581776783189334, 360581776350204214, 360581776008669174, 360581776211200923, 360581776391563731, 360581776763024358]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 36580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 36500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360573323359357815, 360573331551038022⟩, ⟨308835086081959350, 309037762189648584⟩, true⟩

def words09 : List Nat := [360581776763462868, 360581776758569404, 360581776753582858, 360581777070749979, 360581777071163952, 360581777037132517, 360581777003043539, 360581776411736869, 360581775435887850, 360581775205742658]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 36590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 36500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 36500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk365B
