import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk629A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk629B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk629A

def state06 : KState := ⟨⟨360592794188869224, 360592819521973535⟩, ⟨(-639302751438380573), (-638225299547515221)⟩, true⟩

def words05 : List Nat := [360582682011343339, 360582682330199838, 360582682591364148, 360582682601329329, 360582682602152203, 360582682393478753, 360582682184642626, 360582682362831290, 360582682524559721, 360582682686479380]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 62950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 62900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360582370293347434, 360582395634868426⟩, ⟨16872100208320590, 17950082054440810⟩, true⟩

def words06 : List Nat := [360582682710512356, 360582682711396695, 360582682484037723, 360582682443520623, 360582682402766841, 360582682183212853, 360582681853305622, 360582681382418756, 360582680911375090, 360582680692547551]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 62960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 62900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560422102030784, 360560447451890497⟩, ⟨1399177535911540615, 1400256042888992225⟩, true⟩

def words07 : List Nat := [360582680936108716, 360582681184377912, 360582681307270477, 360582681391856508, 360582681392602516, 360582681304188747, 360582681306818992, 360582681307703472, 360582681148602142, 360582680796490196]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 62970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 62900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360630767585641598, 360630792943851627⟩, ⟨(-3031537676759548469), (-3030458643838092665)⟩, true⟩

def words08 : List Nat := [360582680444188603, 360582680370798281, 360582680650136075, 360582680929634446, 360582680991350306, 360582681188872735, 360582681637995251, 360582682087363927, 360582682788247180, 360582683552925335]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 62980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 62900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617278621413811, 360617303988071037⟩, ⟨(-2181832536322976280), (-2180752971272045690)⟩, true⟩

def words09 : List Nat := [360582684188660193, 360582684824464088, 360582685453568626, 360582686208568265, 360582686858393501, 360582687508342191, 360582687946705493, 360582688310334693, 360582688860505458, 360582689410980641]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 62990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 62900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 62900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk629B
