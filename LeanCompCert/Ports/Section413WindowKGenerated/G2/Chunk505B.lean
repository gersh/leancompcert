import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk505A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk505B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk505A

def state06 : KState := ⟨⟨360587950916831977, 360587966968117015⟩, ⟨(-303202537636786068), (-302654171145249614)⟩, true⟩

def words05 : List Nat := [360581977888515208, 360581978459022930, 360581978773771252, 360581979238173822, 360581979604506954, 360581979971015598, 360581980453048042, 360581980808596385, 360581980927616836, 360581981046732050]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 50550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 50500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360602855410522590, 360602871468407311⟩, ⟨(-1056912104866573627), (-1056363404662809905)⟩, true⟩

def words06 : List Nat := [360581981058293049, 360581981288989002, 360581981777661009, 360581982266447286, 360581982420277536, 360581982420975953, 360581982287168028, 360581982213071559, 360581982335692428, 360581982749484158]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 50560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 50500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360603016618629662, 360603032683168830⟩, ⟨(-1065097604935716412), (-1064548568184352992)⟩, true⟩

def words07 : List Nat := [360581982966171979, 360581983182921366, 360581983697145831, 360581984408894361, 360581984770100212, 360581985131393969, 360581985243258705, 360581985437524901, 360581985854207946, 360581986271113230]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 50570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 50500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360618713703455802, 360618729774579152⟩, ⟨(-1859080647175063541), (-1858531277362016945)⟩, true⟩

def words08 : List Nat := [360581987077809123, 360581987895931048, 360581988466344093, 360581989036807942, 360581989439482958, 360581990039460052, 360581991029201038, 360581992019036663, 360581992646412585, 360581993373295090]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 50580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 50500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360668456515133022, 360668472592855208⟩, ⟨(-4375837921092751172), (-4375288217412281984)⟩, true⟩

def words09 : List Nat := [360581994489936792, 360581995606741798, 360581997113225988, 360581998397554745, 360581999347677918, 360582000297833447, 360582001416208995, 360582002736080574, 360582004445536053, 360582006155088914]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 50590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 50500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 50500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk505B
