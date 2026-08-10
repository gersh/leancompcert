import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk740A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk740B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk740A

def state06 : KState := ⟨⟨360571864008196483, 360571899517455721⟩, ⟨773286763573284816, 775063025768748106⟩, true⟩

def words05 : List Nat := [360582367398300461, 360582367243836252, 360582367089060350, 360582366885353928, 360582366557930335, 360582366074854700, 360582365591590613, 360582365248437789, 360582364996918177, 360582364856718059]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 74050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 74000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360554714491717338, 360554750011013175⟩, ⟨2043367883077274085, 2045144888633286737⟩, true⟩

def words06 : List Nat := [360582364716363701, 360582364457184983, 360582364120057588, 360582363811574955, 360582363502821658, 360582363148280273, 360582362697985011, 360582362106453165, 360582361514738020, 360582360985613328]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 74060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 74000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360563139495385720, 360563175024596646⟩, ⟨1419378145003153393, 1421155885019893379⟩, true⟩

def words07 : List Nat := [360582360613701394, 360582360423949456, 360582360234087626, 360582359953437213, 360582359833436062, 360582359667837763, 360582359517104531, 360582359518157924, 360582359352196149, 360582359094318837]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 74070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 74000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360567334610205876, 360567370149381208⟩, ⟨1108538159424733071, 1110316637652937783⟩, true⟩

def words08 : List Nat := [360582358836226583, 360582358513631938, 360582358282550809, 360582358136494891, 360582357990367783, 360582357665829282, 360582357281015451, 360582356882304156, 360582356483262236, 360582356201988213]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 74080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 74000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360563717157356388, 360563752706562316⟩, ⟨1376580648804540735, 1378359870248322175⟩, true⟩

def words09 : List Nat := [360582356000661628, 360582355708571735, 360582355416288042, 360582355306160284, 360582355301751207, 360582355143922754, 360582354985985473, 360582354736164941, 360582354304161002, 360582354054338947]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 74090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 74000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 74000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk740B
