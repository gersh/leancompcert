import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk930A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk930B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk930A

def state06 : KState := ⟨⟨360586474426376444, 360586531499628592⟩, ⟨(-423018152098206978), (-419431659592044442)⟩, true⟩

def words05 : List Nat := [360582025257572767, 360582025042989801, 360582024828152843, 360582024729132669, 360582024703197051, 360582024623334641, 360582024543326982, 360582024405479251, 360582024388034754, 360582024438028222]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360586996070904676, 360587053156823694⟩, ⟨(-471573315033096979), (-467985643684346809)⟩, true⟩

def words06 : List Nat := [360582024549805351, 360582024660886508, 360582024703830022, 360582024746919480, 360582024748066234, 360582024730913591, 360582024785948719, 360582024841235990, 360582024842448404, 360582024891911054]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360594353352116658, 360594410450768118⟩, ⟨(-1156375104171776142), (-1152786247751594254)⟩, true⟩

def words07 : List Nat := [360582024964651582, 360582025037804601, 360582025201682091, 360582025275560038, 360582025276807223, 360582025240177347, 360582025280664229, 360582025417825305, 360582025551991053, 360582025686447241]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360609745184041315, 360609802295511158⟩, ⟨(-2589222817013511558), (-2585632767394687278)⟩, true⟩

def words08 : List Nat := [360582025732225504, 360582025760219831, 360582025903279389, 360582026046731518, 360582026160901550, 360582026302591132, 360582026386862869, 360582026471268612, 360582026670733036, 360582026970642002]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590686660316756, 360590743784501004⟩, ⟨(-814931519760085283), (-811340286497447597)⟩, true⟩

def words09 : List Nat := [360582027361783920, 360582027753180079, 360582028041326587, 360582028243776730, 360582028396277300, 360582028549146845, 360582028816904329, 360582028969832005, 360582029064639436, 360582029159668860]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk930B
