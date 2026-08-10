import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk944A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk944B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk944A

def state06 : KState := ⟨⟨360600906949998404, 360600965821629447⟩, ⟨(-1785903179558296909), (-1782148067830805349)⟩, true⟩

def words05 : List Nat := [360582098131870995, 360582098298752762, 360582098525709307, 360582098669112866, 360582098716728243, 360582098764437242, 360582098798736068, 360582098923757004, 360582099124597461, 360582099325744047]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 94450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 94400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588167565348025, 360588226450002332⟩, ⟨(-582555432152516888), (-578799090183541166)⟩, true⟩

def words06 : List Nat := [360582099443331207, 360582099478056976, 360582099624542120, 360582099771440970, 360582099841362239, 360582099842730746, 360582099826354824, 360582099753877297, 360582099681129621, 360582099711742088]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 94460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 94400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360563253174778351, 360563312072332744⟩, ⟨1771253536115953575, 1775011096821203973⟩, true⟩

def words07 : List Nat := [360582099785128287, 360582099858793925, 360582099875414864, 360582099876783418, 360582099781686744, 360582099658721413, 360582099535356638, 360582099524246566, 360582099432094751, 360582099234661504]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 94470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 94400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360603730908578709, 360603789819057046⟩, ⟨(-2053291140224470114), (-2049532358402535432)⟩, true⟩

def words08 : List Nat := [360582099036921858, 360582098929146201, 360582098960774880, 360582099033399331, 360582099034661504, 360582099038823793, 360582099115690338, 360582099192956242, 360582099349237933, 360582099580215225]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 94480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 94400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360595554683936442, 360595613607471687⟩, ⟨(-1280694691781687327), (-1276934676150755221)⟩, true⟩

def words09 : List Nat := [360582099755139031, 360582099930197221, 360582100102394858, 360582100330675065, 360582100530209316, 360582100729962873, 360582100859502563, 360582100925510917, 360582101069608948, 360582101214204412]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 94490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 94400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 94400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk944B
